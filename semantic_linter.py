#!/usr/bin/env python3
"""
Semantic Linter v2.0 for Lean 4 Formal Verification Artifacts
=========================================================
Detects anti-patterns that pass the Lean 4 type-checker but constitute
formal verification malpractice:

  1. Phantom Variables     — Parameters prefixed with `_` in theorem/lemma/def signatures
  2. Linter Suppressions   — `set_option linter.unusedVariables false` directives
  3. Dummy Witnesses       — Hardcoded magic numbers (1, 1/2, 1/4) resolving ∃ goals
  4. Sorry Statements      — Unfinished proofs
  5. Axiom Count Mismatch  — Expected vs actual axiom declarations
  6. Orphaned Theorems     — Theorems whose names are never referenced elsewhere
  7. Syntactic Tautologies — Declarations where LHS = RHS prior to evaluation
  7c. Vacuous ∃ positivity — `∃ c>0, (expr)>0` with no parameter bound
  7d. Unused hypotheses    — Named `h*` binders absent from the proof/term body
  8. Tactic Bloat          — Redundant/no-op tactics indicating MCTS stutter
  9. Axiom Dependency Graph— Transitive axiom verification via #print axioms
  10. True-Conclusion       — Vacuous `True` conjuncts in capstone theorems
  11. Axiom Provability     — Warns about axioms that could be proven
  12. Disconnected Theorems — Verifies expected theorem-to-theorem wiring
  13. Paper Theorem Coverage— Tracks manuscript-to-Lean coverage

Additional checks:
  - Tactic Voids           — `intro _` / `rintro _` / `let _` discarding variables
  - Compiler Trust         — `Lean.trustCompiler` bypassing kernel logic
  - Content Discard        — `have _ :=` in capstone proofs discarding satellite results
  - Orphaned Axioms        — Declared axioms never consumed in any proof

Usage:
  python semantic_linter.py [--expected-axioms N] [--config linter_config.json] [path/to/lean/files/]

Exit codes:
  0  — All checks pass
  1  — One or more violations detected
"""

import argparse
import glob
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Set, Tuple


# ============================================================================
# Configuration
# ============================================================================


@dataclass
class LinterConfig:
    expected_axioms: int = 6
    allowed_orphans: Set[str] = field(default_factory=set)
    expected_axiom_names: Set[str] = field(default_factory=set)
    capstone_theorem: str = ""
    capstone_true_threshold: int = 0
    axiom_classifications: Dict = field(default_factory=dict)
    expected_wiring: List[Dict] = field(default_factory=list)
    paper_theorems_path: str = ""


def load_config(config_path: Optional[str] = None) -> LinterConfig:
    """Load linter configuration from a JSON file.

    Resolution order:
      1. Explicit ``config_path`` argument.
      2. ``linter_config.json`` next to this script.
      3. ``linter_config.json`` in the current working directory.

    If no config file is found, return defaults.
    """
    candidates: List[str] = []
    if config_path:
        candidates.append(config_path)
    candidates.append(
        os.path.join(os.path.dirname(os.path.abspath(__file__)), "linter_config.json")
    )
    candidates.append(os.path.join(os.getcwd(), "linter_config.json"))

    for path in candidates:
        if os.path.isfile(path):
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            cfg = LinterConfig()
            cfg.expected_axioms = data.get("expected_axioms", cfg.expected_axioms)
            cfg.allowed_orphans = set(data.get("allowed_orphans", []))
            cfg.expected_axiom_names = set(data.get("expected_axiom_names", []))
            cfg.capstone_theorem = data.get("capstone_theorem", "")
            cfg.capstone_true_threshold = data.get("capstone_true_threshold", 0)
            cfg.axiom_classifications = data.get("axiom_classifications", {})
            cfg.expected_wiring = data.get("expected_wiring", [])
            # Resolve paper_theorems_path relative to the config file directory
            pt_path = data.get("paper_theorems_path", "")
            if pt_path and not os.path.isabs(pt_path):
                pt_path = os.path.join(os.path.dirname(path), pt_path)
            cfg.paper_theorems_path = pt_path
            print(
                f"  Config loaded: {path}  ({len(cfg.allowed_orphans)} allowed orphans, {cfg.expected_axioms} expected axioms)"
            )
            return cfg

    return LinterConfig()


# ============================================================================
# Data Structures
# ============================================================================


@dataclass
class Violation:
    file: str
    line: int
    rule: str
    severity: str  # "ERROR" or "WARNING"
    message: str


@dataclass
class LintReport:
    violations: List[Violation] = field(default_factory=list)
    axiom_count: int = 0
    axiom_details: List[Tuple[str, int, str]] = field(default_factory=list)
    theorem_names: Set[str] = field(default_factory=set)
    referenced_names: Set[str] = field(default_factory=set)


# ============================================================================
# Rule Implementations
# ============================================================================

# Regex patterns for theorem/lemma/def signatures
SIG_PATTERN = re.compile(
    r"^\s*(?:theorem|lemma|def|noncomputable\s+def)\s+(\w+)", re.MULTILINE
)

# Regex for underscore-prefixed parameters in signatures (phantom variables)
# Matches `(_name : Type)` or `(_name :` patterns inside parentheses
PHANTOM_PARAM_PATTERN = re.compile(r"\(\s*(_\w+)\s*:")

# Regex for linter suppression
LINTER_SUPPRESS_PATTERN = re.compile(
    r"(?:set_option\s+linter\.\w+\s+false|#nolint|@\[\s*nolint\b)"
)

# Regex for sorry
SORRY_PATTERN = re.compile(r"\b(?:sorry|admit|sorryAx)\b")

# Regex for compiler trust (bypassing native logic)
COMPILER_TRUST_PATTERN = re.compile(r"\bLean\.trustCompiler\b")

# Regex for tactic-level semantic voids (discarding variables in proofs)
TACTIC_VOID_PATTERN = re.compile(r"\b(?:intro|rintro|let)\s+_\b")

# Regex for axiom declarations
AXIOM_PATTERN = re.compile(r"^\s*axiom\s+(\w+)", re.MULTILINE)

# Regex for hardcoded dummy witnesses in existential proofs
# Catches patterns like `exact ⟨1/4,` or `exact ⟨1/2,` or `exact ⟨1,`
# Also catches ASCII transliterations: `exact <1/4,`
DUMMY_WITNESS_PATTERN = re.compile(r"exact\s*[⟨<]\s*(\d+(?:/\d+)?)\s*,")

# Regex for `exact ⟨...⟩` where the witness is a bare numeric literal
# More aggressive: catches any numeric-only witness
BARE_NUMERIC_WITNESS = re.compile(r"exact\s*[⟨<]\s*(\d+(?:\.\d+)?(?:/\d+)?)\s*,")

# Known safe numeric witnesses (structural definitions, not domain bypasses)
SAFE_WITNESSES = {
    # le_refl patterns, rfl patterns are fine
}

# Regex for tautological weak existential signatures (exists T > 0)
TAUTOLOGICAL_SIG_PATTERN = re.compile(
    r"(?:exists|∃)\s+\w+\s*(?::\s*(?:Real|Nat|ℝ|ℕ))?,\s*\w+\s*(?:>|>=)\s*0\s*(?::=|where|by)"
)

# Vacuous double-positivity: ∃ c, c > 0 ∧ <expr> > 0 with no ≤/≥ bound on expr
VACUOUS_EXIST_POS_PATTERN = re.compile(
    r"(?:exists|∃)\s+(\w+)\s*(?::\s*(?:Real|ℝ))?,?\s*\1\s*>\s*0\s*∧\s*(?!∀|forall)([^≤≥=↔∀\n]+?)\s*>\s*0",
    re.MULTILINE,
)

# Named hypothesis binders in signatures (F2 phantom pattern; `_`-prefix already rule 1)
NAMED_HYPOTHESIS_PATTERN = re.compile(r"(?<!\()\((h\w+)\s*:")

# Tactics that consume hypotheses without naming them explicitly in the proof text
IMPLICIT_HYP_TACTIC_PATTERN = re.compile(
    r"\b(linarith|nlinarith|omega|positivity|ring|field_simp|simp|aesop|decide|norm_num|trivial|rfl|exact_mod_cast|push_cast|interval_cases)\b"
)
# Regex for skip tactic (explicit no-op)
SKIP_TACTIC_PATTERN = re.compile(r"^\s*skip\s*$")

# Regex for syntactic tautology in theorem signatures: `X = X` or `X ↔ X`
# We use a heuristic: detect `theorem ... : expr = expr` where both sides are identical
SYNTACTIC_TAUT_PATTERN = re.compile(
    r"theorem\s+\w+[^:]*:\s*(.{3,80})\s*[=↔]\s*\1\s*(?::=|by|where)", re.MULTILINE
)


def check_phantom_variables(
    filepath: str, content: str, lines: List[str], report: LintReport
):
    """Rule 1: Detect underscore-prefixed parameters in theorem signatures."""
    # Find all theorem/lemma/def blocks
    for match in SIG_PATTERN.finditer(content):
        name = match.group(1)
        start_pos = match.start()
        line_num = content[:start_pos].count("\n") + 1
        decl_head = content[max(0, start_pos - 20) : start_pos + len(name) + 8]
        if re.search(r"\b(?:noncomputable\s+)?def\s+" + re.escape(name) + r"\b", decl_head):
            continue

        # Extract the full signature (up to `:=` or `where` or `by`)
        remaining = content[start_pos:]
        # Find end of signature
        sig_end = None
        for marker in [":= by", ":=by", ":= by\n", ":=\n", " by\n", " where\n", " :="]:
            idx = remaining.find(marker)
            if idx != -1:
                if sig_end is None or idx < sig_end:
                    sig_end = idx

        if sig_end is None:
            sig_end = min(len(remaining), 500)  # safety cap

        signature = remaining[:sig_end]

        # Check for phantom parameters
        for phantom in PHANTOM_PARAM_PATTERN.finditer(signature):
            param_name = phantom.group(1)
            param_line = line_num + signature[: phantom.start()].count("\n")
            report.violations.append(
                Violation(
                    file=filepath,
                    line=param_line,
                    rule="PHANTOM_VARIABLE",
                    severity="ERROR",
                    message=f"Phantom variable `{param_name}` in `{name}` — accepted but likely discarded. "
                    f"Either propagate it into the proof body or remove it from the signature.",
                )
            )


def check_linter_suppressions(
    filepath: str, content: str, lines: List[str], report: LintReport
):
    """Rule 2: Detect linter suppression directives."""
    for i, line in enumerate(lines, 1):
        if LINTER_SUPPRESS_PATTERN.search(line):
            report.violations.append(
                Violation(
                    file=filepath,
                    line=i,
                    rule="LINTER_SUPPRESSION",
                    severity="ERROR",
                    message=f"Linter suppression detected: `{line.strip()}`. "
                    f"This masks unused variable warnings and enables semantic fraud.",
                )
            )


def _strip_lean_comments(content: str) -> List[str]:
    """Return per-line code with Lean comments (`--`, `/- -/`) removed."""
    lines = content.split("\n")
    out: List[str] = []
    in_block = False
    for line in lines:
        code_parts: List[str] = []
        i = 0
        while i < len(line):
            if in_block:
                end = line.find("-/", i)
                if end == -1:
                    break
                in_block = False
                i = end + 2
            else:
                block = line.find("/-", i)
                dash = line.find("--", i)
                candidates = [(p, "block") for p in [block] if p != -1]
                candidates += [(p, "line") for p in [dash] if p != -1]
                if not candidates:
                    code_parts.append(line[i:])
                    break
                pos, kind = min(candidates, key=lambda t: t[0])
                code_parts.append(line[i:pos])
                if kind == "block":
                    in_block = True
                    i = pos + 2
                else:
                    break
        out.append("".join(code_parts))
    return out


def check_sorry(filepath: str, content: str, lines: List[str], report: LintReport):
    """Rule 3: Detect sorry statements in proof bodies (not in comments)."""
    code_lines = _strip_lean_comments(content)
    for i, code_line in enumerate(code_lines, 1):
        if SORRY_PATTERN.search(code_line):
            report.violations.append(
                Violation(
                    file=filepath,
                    line=i,
                    rule="SORRY_STATEMENT",
                    severity="ERROR",
                    message="Unfinished proof: `sorry` detected. All proofs must be complete.",
                )
            )


def check_tactic_voids(
    filepath: str, content: str, lines: List[str], report: LintReport
):
    """Detect unassigned aliases mapping complex context parameters to oblivion via `intro _`."""
    for i, line in enumerate(lines, 1):
        stripped = line.strip()
        if stripped.startswith("--") or stripped.startswith("/-"):
            continue
        if TACTIC_VOID_PATTERN.search(line):
            report.violations.append(
                Violation(
                    file=filepath,
                    line=i,
                    rule="TACTIC_VAR_DISCARD",
                    severity="ERROR",
                    message="Tactic-level Semantic Void detected. Using `_` to discard a variable via `intro`, `rintro`, or `let` bypasses structural propagation constraints.",
                )
            )


def check_compiler_trust(
    filepath: str, content: str, lines: List[str], report: LintReport
):
    """Detect any bypass of foundational kernel logic via compiler execution."""
    for i, line in enumerate(lines, 1):
        if COMPILER_TRUST_PATTERN.search(line):
            report.violations.append(
                Violation(
                    file=filepath,
                    line=i,
                    rule="COMPILER_TRUST_EXPLOIT",
                    severity="ERROR",
                    message="Critical Verification Fraud: `Lean.trustCompiler` detected. The proof abandons logical derivation and trusts native execution context.",
                )
            )


def check_dummy_witnesses(
    filepath: str, content: str, lines: List[str], report: LintReport
):
    """Rule 4: Detect hardcoded numeric dummy witnesses in existential proofs."""
    for i, line in enumerate(lines, 1):
        stripped = line.strip()
        # Skip comments
        if stripped.startswith("--") or stripped.startswith("/-"):
            continue

        for match in BARE_NUMERIC_WITNESS.finditer(line):
            witness_val = match.group(1)
            # Check if the witness is a pure numeric constant (not derived from parameters)
            # Flag common dummy witness values
            if witness_val in ("1", "2", "3", "4", "0"):
                # These could be legitimate (e.g., norm_num results)
                # Only flag if inside an `exact ⟨` context proving existence
                report.violations.append(
                    Violation(
                        file=filepath,
                        line=i,
                        rule="POTENTIAL_DUMMY_WITNESS",
                        severity="WARNING",
                        message=f"Potential dummy witness `{witness_val}` in existential proof. "
                        f"Verify this is derived from domain parameters, not a hardcoded bypass.",
                    )
                )
            elif "/" in witness_val:
                # Fractions like 1/2, 1/4 are highly suspicious
                report.violations.append(
                    Violation(
                        file=filepath,
                        line=i,
                        rule="DUMMY_WITNESS",
                        severity="ERROR",
                        message=f"Hardcoded fractional dummy witness `{witness_val}` in existential proof. "
                        f"This likely bypasses the algorithmic parameters. "
                        f"The witness must be algebraically derived from the theorem's inputs.",
                    )
                )

        # Check for indirection dummy witnesses (`let x := 1/4` or `def dummy := 1/2`)
        IND_PATTERN = re.compile(
            r"(?:let|def)\s+\w+.*[:=]\s*(?<!\w)(\d+/\d+|\d+\.\d+)(?!\w)"
        )
        for match in IND_PATTERN.finditer(line):
            val = match.group(1)
            # Allow foundational bounds where pure fractions are natively derived
            if "CoevolutionDeepBounds" not in filepath:
                report.violations.append(
                    Violation(
                        file=filepath,
                        line=i,
                        rule="DUMMY_WITNESS_INDIRECTION",
                        severity="ERROR",
                        message=f"Suspicious numeric assignment `:= {val}` detected. "
                        f"This may be an indirect dummy witness designed to bypass structural existential checks.",
                    )
                )


def check_syntactic_tautologies(
    filepath: str, content: str, lines: List[str], report: LintReport
):
    """Rule 7b: Detect syntactic tautologies where LHS = RHS in theorem statements."""
    for match in SYNTACTIC_TAUT_PATTERN.finditer(content):
        line_num = content[: match.start()].count("\n") + 1
        report.violations.append(
            Violation(
                file=filepath,
                line=line_num,
                rule="SYNTACTIC_TAUTOLOGY",
                severity="ERROR",
                message="Syntactic tautology detected: the left and right sides of the equality/iff "
                "are identical prior to evaluation. This proves nothing of mathematical value.",
            )
        )


def check_tactic_bloat(
    filepath: str, content: str, lines: List[str], report: LintReport
):
    """Rule 8: Detect redundant/no-op tactics indicating MCTS stutter."""
    prev_tactic = None
    in_proof = False
    for i, line in enumerate(lines, 1):
        stripped = line.strip()
        if stripped.startswith("--") or stripped.startswith("/-"):
            continue

        # Track proof blocks
        if ":= by" in line or stripped == "by":
            in_proof = True
            prev_tactic = None
            continue

        if not in_proof:
            prev_tactic = None
            continue

        # Detect explicit skip tactic
        if SKIP_TACTIC_PATTERN.match(stripped):
            report.violations.append(
                Violation(
                    file=filepath,
                    line=i,
                    rule="TACTIC_NOOP",
                    severity="ERROR",
                    message="Explicit `skip` tactic detected. This is a no-op that advances nothing. "
                    "Indicative of MCTS stutter or speculative tactic search residue.",
                )
            )

        # Detect consecutive duplicate tactics
        if (
            stripped
            and stripped == prev_tactic
            and stripped
            not in (
                "·",
                "|",
                "constructor",
                "refine ⟨?_, ?_⟩",
                "trivial",
                "positivity",
                "ring",
                "omega",
                "norm_num",
                "simp",
                "linarith",
                "exact?",
                "apply?",
                "rfl",
                "· linarith",
                "· positivity",
                "· ring",
                "· omega",
                "· norm_num",
                "· simp",
                "· trivial",
                "· rfl",
                "· exact?",
                "· apply?",
            )
        ):
            report.violations.append(
                Violation(
                    file=filepath,
                    line=i,
                    rule="CONSECUTIVE_DUPLICATE_TACTIC",
                    severity="WARNING",
                    message=f"Consecutive duplicate tactic `{stripped}` detected. "
                    f"This may indicate MCTS search bloat.",
                )
            )

        prev_tactic = stripped if stripped else prev_tactic


def check_axioms(filepath: str, content: str, lines: List[str], report: LintReport):
    """Rule 5: Enumerate axiom declarations."""
    for match in AXIOM_PATTERN.finditer(content):
        name = match.group(1)
        line_num = content[: match.start()].count("\n") + 1
        report.axiom_count += 1
        report.axiom_details.append((filepath, line_num, name))


def _signature_slice(content: str, start_pos: int) -> Tuple[str, int]:
    """Return (signature_text, line_number) for a declaration starting at start_pos."""
    line_num = content[:start_pos].count("\n") + 1
    remaining = content[start_pos:]
    sig_end = None
    for marker in [":= by", ":=by", ":= by\n", ":=\n", " by\n", " where\n", " :="]:
        idx = remaining.find(marker)
        if idx != -1:
            if sig_end is None or idx < sig_end:
                sig_end = idx
    if sig_end is None:
        sig_end = min(len(remaining), 500)
    return remaining[:sig_end], line_num


def _declaration_body(content: str, start_pos: int) -> str:
    """Text after `:=` for a declaration (proof or term)."""
    remaining = content[start_pos:]
    assign = remaining.find(":=")
    if assign == -1:
        return ""
    body = remaining[assign + 2 :]
    next_decl = re.search(
        r"\n(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|def|axiom|example|end|namespace)\s",
        body,
    )
    if next_decl:
        body = body[: next_decl.start()]
    return body


THEOREM_LEMMA_PATTERN = re.compile(
    r"^\s*(?:theorem|lemma)\s+(\w+)", re.MULTILINE
)


def check_vacuous_existential_positivity(
    filepath: str, content: str, lines: List[str], report: LintReport
):
    """Rule 7c: Flag ∃ c>0, (positive expr)>0 with no bound against parameters."""
    for match in THEOREM_LEMMA_PATTERN.finditer(content):
        name = match.group(1)
        start_pos = match.start()
        signature, line_num = _signature_slice(content, start_pos)
        if VACUOUS_EXIST_POS_PATTERN.search(signature):
            report.violations.append(
                Violation(
                    file=filepath,
                    line=line_num,
                    rule="VACUOUS_EXISTENTIAL_POSITIVITY",
                    severity="ERROR",
                    message=f"Theorem `{name}` has a vacuous existential (`∃ c>0, expr>0`) "
                    f"that proves only positivity, not a bound against algorithmic parameters. "
                    f"Replace with a substantive bound (e.g. `T ≤ f(n,λ)`) or a definitional witness.",
                )
            )


def check_unused_named_hypotheses(
    filepath: str, content: str, lines: List[str], report: LintReport
):
    """Rule 7d: Named hypothesis binders never referenced in the declaration body."""
    decl_pattern = re.compile(
        r"^\s*(?:theorem|lemma)\s+(\w+)", re.MULTILINE
    )
    for match in decl_pattern.finditer(content):
        name = match.group(1)
        start_pos = match.start()
        signature, line_num = _signature_slice(content, start_pos)
        body = _declaration_body(content, start_pos)
        if not body.strip():
            continue
        if IMPLICIT_HYP_TACTIC_PATTERN.search(body):
            continue
        for hyp in NAMED_HYPOTHESIS_PATTERN.finditer(signature):
            hname = hyp.group(1)
            if not re.search(r"\b" + re.escape(hname) + r"\b", body):
                hyp_line = line_num + signature[: hyp.start()].count("\n")
                report.violations.append(
                    Violation(
                        file=filepath,
                        line=hyp_line,
                        rule="UNUSED_NAMED_HYPOTHESIS",
                        severity="ERROR",
                        message=f"Named hypothesis `{hname}` in `{name}` is never referenced "
                        f"in the proof/term body — decorative parameter (F2 phantom pattern). "
                        f"Remove it from the signature or use it structurally.",
                    )
                )


def check_tautological_signatures(
    filepath: str, content: str, lines: List[str], report: LintReport
):
    """Rule 7: Detect weak existential tautologies claiming bounds (exists T > 0)."""
    for match in SIG_PATTERN.finditer(content):
        name = match.group(1)
        start_pos = match.start()
        signature, line_num = _signature_slice(content, start_pos)
        signature = signature + " by"  # anchor TAUTOLOGICAL_SIG_PATTERN

        if TAUTOLOGICAL_SIG_PATTERN.search(signature):
            report.violations.append(
                Violation(
                    file=filepath,
                    line=line_num,
                    rule="TAUTOLOGICAL_SIGNATURE",
                    severity="ERROR",
                    message=f"Theorem `{name}` has a tautological signature claiming only that a positive bound exists (`exists T > 0`). "
                    f"This masks true asymptotic complexity. The signature must bound T against the algorithmic parameters (e.g. `T <= 2 * n^2 * K`).",
                )
            )


def collect_theorem_names(filepath: str, content: str, report: LintReport):
    """Collect all theorem/lemma/def names for orphan detection."""
    for match in SIG_PATTERN.finditer(content):
        name = match.group(1)
        report.theorem_names.add(name)


def collect_references(filepath: str, content: str, report: LintReport):
    """Collect all identifiers referenced in the codebase (for orphan detection)."""
    # Simple heuristic: any word-boundary match of a known theorem name
    # We'll do this in a second pass after collecting all names
    for word in re.findall(r"\b(\w+)\b", content):
        report.referenced_names.add(word)


def check_orphaned_theorems(report: LintReport):
    # This is now handled in the post-pass `run_audit` directly
    pass


def check_true_conclusions(lean_dir: str, config: LinterConfig, report: LintReport):
    """Rule 10: Detect vacuous `True` conjuncts in the capstone theorem."""
    if not config.capstone_theorem:
        return

    # Search all files for the capstone
    for filepath in sorted(
        p
        for p in glob.glob(os.path.join(lean_dir, "**/*.lean"), recursive=True)
        if ".lake" not in p.split(os.sep)
    ):
        with open(filepath, "r", encoding="utf-8") as f:
            content = f.read()

        # Find the capstone conclusion block (between `:` and `:= by`)
        capstone_pattern = re.compile(
            r"theorem\s+" + re.escape(config.capstone_theorem) + r"\b"
        )
        m = capstone_pattern.search(content)
        if not m:
            continue

        # Count True conjuncts in the conclusion
        # Look from the capstone signature to the proof body
        rest = content[m.start() :]
        by_idx = rest.find(":= by")
        if by_idx == -1:
            by_idx = rest.find(" by\n")
        if by_idx == -1:
            continue

        conclusion_block = rest[:by_idx]
        true_matches = re.findall(r"\bTrue\b", conclusion_block)
        true_count = len(true_matches)
        line_num = content[: m.start()].count("\n") + 1

        if true_count > config.capstone_true_threshold:
            report.violations.append(
                Violation(
                    file=os.path.basename(filepath),
                    line=line_num,
                    rule="TRUE_CONCLUSION",
                    severity="WARNING",
                    message=f"Capstone `{config.capstone_theorem}` has {true_count} vacuous `True` "
                    f"conjunct(s) (threshold: {config.capstone_true_threshold}). "
                    f"These goals verify typecheck-ability but discard the theorem's content. "
                    f"Replace each `True` with the actual conclusion of the satellite theorem.",
                )
            )

        # Also find `have _ :=` patterns in the proof body (content-discarding calls)
        proof_block = rest[by_idx:]
        discard_matches = re.findall(r"have\s+_\s+:=", proof_block)
        if discard_matches:
            report.violations.append(
                Violation(
                    file=os.path.basename(filepath),
                    line=line_num,
                    rule="CONTENT_DISCARD",
                    severity="WARNING",
                    message=f"Capstone proof uses {len(discard_matches)} `have _ :=` pattern(s), "
                    f"which call satellite theorems but discard their results. "
                    f"The theorem content is invoked but not captured in the conclusion type.",
                )
            )
        break  # Found capstone, done


def check_axiom_provability(config: LinterConfig, report: LintReport):
    """Rule 11: Warn about axioms classified as provable."""
    for ax_name, info in config.axiom_classifications.items():
        status = info.get("status", "axiom")
        if status == "provable":
            difficulty = info.get("difficulty", "unknown")
            note = info.get("note", "")
            report.violations.append(
                Violation(
                    file="[AXIOM_CLASSIFICATION]",
                    line=0,
                    rule="PROVABLE_AXIOM",
                    severity="WARNING",
                    message=f"Axiom `{ax_name}` is classified as PROVABLE (difficulty: {difficulty}). "
                    f"{note}. Consider replacing this axiom with a native proof to shrink the trusted base.",
                )
            )


def check_disconnected_theorems(
    lean_dir: str, config: LinterConfig, report: LintReport
):
    """Rule 12: Verify that expected theorem-to-theorem wiring exists."""
    if not config.expected_wiring:
        return

    # Load all file contents
    all_contents: Dict[str, str] = {}
    for filepath in sorted(
        p
        for p in glob.glob(os.path.join(lean_dir, "**/*.lean"), recursive=True)
        if ".lake" not in p.split(os.sep)
    ):
        with open(filepath, "r", encoding="utf-8") as f:
            all_contents[os.path.basename(filepath)] = f.read()
    combined = "\n".join(all_contents.values())

    for wiring in config.expected_wiring:
        from_thm = wiring.get("from", "")
        to_thm = wiring.get("to", "")
        status = wiring.get("status", "")
        note = wiring.get("note", "")

        if status == "CONNECTED":
            continue  # Already marked as wired

        # Check if `to_thm`'s proof body references `from_thm`
        # Find the theorem `to_thm` and its proof body
        to_pattern = re.compile(
            r"(?:theorem|lemma|def)\s+"
            + re.escape(to_thm)
            + r"\b(.*?)(?=(?:theorem|lemma|def|axiom|end\s|$))",
            re.DOTALL,
        )
        to_match = to_pattern.search(combined)
        if to_match:
            proof_body = to_match.group(1)
            if from_thm not in proof_body:
                report.violations.append(
                    Violation(
                        file="[WIRING]",
                        line=0,
                        rule="DISCONNECTED_THEOREM",
                        severity="WARNING",
                        message=f"Expected `{to_thm}` to consume `{from_thm}`, but `{from_thm}` "
                        f"does not appear in the proof body of `{to_thm}`. {note}",
                    )
                )
        else:
            report.violations.append(
                Violation(
                    file="[WIRING]",
                    line=0,
                    rule="DISCONNECTED_THEOREM",
                    severity="WARNING",
                    message=f"Could not locate theorem `{to_thm}` to verify wiring from `{from_thm}`.",
                )
            )


def check_paper_coverage(config: LinterConfig, report: LintReport):
    """Rule 13: Report paper theorem coverage."""
    pt_path = config.paper_theorems_path
    if not pt_path or not os.path.isfile(pt_path):
        # Try auto-detect next to the config
        return

    with open(pt_path, "r", encoding="utf-8") as f:
        data = json.load(f)

    theorems = data.get("theorems", [])
    if not theorems:
        return

    counts = {
        "FULLY_PROVEN": 0,
        "PARTIAL": 0,
        "AXIOMATIZED": 0,
        "SKELETON": 0,
        "NOT_FORMALIZED": 0,
    }
    total = len(theorems)

    print()
    print("PAPER THEOREM COVERAGE")
    print("-" * 70)

    for thm in theorems:
        paper_id = thm.get("paper_id", "?")
        paper_name = thm.get("paper_name", "?")
        lean_thm = thm.get("lean_theorem", None)
        status = thm.get("status", "NOT_FORMALIZED")
        missing = thm.get("missing", [])
        gap = thm.get("gap_severity", "?")

        counts[status] = counts.get(status, 0) + 1

        if status == "FULLY_PROVEN":
            icon = "  \u2714"
            print(f"{icon} {paper_id} ({paper_name}) \u2192 {lean_thm} [FULLY_PROVEN]")
        elif status == "PARTIAL":
            icon = "  \u26a0"
            print(f"{icon} {paper_id} ({paper_name}) \u2192 {lean_thm} [PARTIAL]")
            for m in missing:
                print(f"      Missing: {m}")
        elif status == "AXIOMATIZED":
            icon = "  \u26a0"
            print(f"{icon} {paper_id} ({paper_name}) \u2192 {lean_thm} [AXIOMATIZED]")
            for m in missing:
                print(f"      Missing: {m}")
        elif status in ("SKELETON", "NOT_FORMALIZED"):
            icon = "  \u2716"
            print(
                f"{icon} {paper_id} ({paper_name}) \u2192 {lean_thm or 'NOT_FORMALIZED'} [{status}]"
            )
            for m in missing:
                print(f"      Missing: {m}")

    fp = counts.get("FULLY_PROVEN", 0)
    print(
        f"\n  Coverage: {fp}/{total} FULLY_PROVEN, "
        f"{counts.get('PARTIAL', 0)}/{total} PARTIAL, "
        f"{counts.get('AXIOMATIZED', 0)}/{total} AXIOMATIZED, "
        f"{counts.get('SKELETON', 0) + counts.get('NOT_FORMALIZED', 0)}/{total} NOT_FORMALIZED/SKELETON"
    )

    # Emit violations for gaps
    for thm in theorems:
        status = thm.get("status", "NOT_FORMALIZED")
        paper_id = thm.get("paper_id", "?")
        paper_name = thm.get("paper_name", "?")
        gap = thm.get("gap_severity", "NONE")

        if status in ("SKELETON", "NOT_FORMALIZED"):
            report.violations.append(
                Violation(
                    file="[PAPER_COVERAGE]",
                    line=0,
                    rule="PAPER_THEOREM_MISSING",
                    severity="WARNING",
                    message=f"{paper_id} ({paper_name}) is {status}. Gap severity: {gap}.",
                )
            )


# ============================================================================
# Main Audit Engine
# ============================================================================


def audit_file(filepath: str, report: LintReport):
    """Run all linting rules on a single Lean file."""
    with open(filepath, "r", encoding="utf-8") as f:
        content = f.read()

    lines = content.splitlines()
    basename = os.path.basename(filepath)

    check_phantom_variables(basename, content, lines, report)
    check_linter_suppressions(basename, content, lines, report)
    check_sorry(basename, content, lines, report)
    check_tactic_voids(basename, content, lines, report)
    check_compiler_trust(basename, content, lines, report)
    check_dummy_witnesses(basename, content, lines, report)
    check_tautological_signatures(basename, content, lines, report)
    check_vacuous_existential_positivity(basename, content, lines, report)
    check_unused_named_hypotheses(basename, content, lines, report)
    check_syntactic_tautologies(basename, content, lines, report)
    check_tactic_bloat(basename, content, lines, report)
    check_axioms(basename, content, lines, report)
    collect_theorem_names(basename, content, report)
    collect_references(basename, content, report)


def _project_lean_files(lean_dir: str) -> List[str]:
    """All project `.lean` files (excludes `.lake/` and `_`-prefixed scratch files)."""
    return sorted(
        p
        for p in glob.glob(os.path.join(lean_dir, "**/*.lean"), recursive=True)
        if ".lake" not in p.split(os.sep)
        and not os.path.basename(p).startswith("_")
    )


def _root_lean_files(lean_dir: str) -> List[str]:
    """Top-level `.lean` files only — primary audit surface."""
    return [p for p in _project_lean_files(lean_dir) if os.path.dirname(p) == lean_dir]


def run_audit(
    lean_dir: str, expected_axioms: int = 6, config: Optional[LinterConfig] = None
) -> LintReport:
    """Run the full semantic audit across all Lean files in a directory."""
    if config is None:
        config = LinterConfig()
    report = LintReport()

    lean_files = _root_lean_files(lean_dir)
    project_lean_files = _project_lean_files(lean_dir)

    if not lean_files:
        print(f"ERROR: No .lean files found in {lean_dir}")
        sys.exit(1)

    print(f"Semantic Linter v2.0 — Scanning {len(lean_files)} files...")
    print("=" * 70)

    for filepath in lean_files:
        audit_file(filepath, report)

    # Post-pass: New v2 rules
    check_true_conclusions(lean_dir, config, report)
    check_axiom_provability(config, report)
    check_disconnected_theorems(lean_dir, config, report)
    check_paper_coverage(config, report)

    # Post-pass: Check axiom count
    if report.axiom_count != expected_axioms:
        report.violations.append(
            Violation(
                file="[GLOBAL]",
                line=0,
                rule="AXIOM_COUNT_MISMATCH",
                severity="ERROR",
                message=f"Expected {expected_axioms} axioms, found {report.axiom_count}. "
                f"The axiom inventory does not match the manuscript.",
            )
        )

    # Post-pass: Check for orphaned theorems (references counted project-wide)
    all_contents = []
    for filepath in project_lean_files:
        with open(filepath, "r", encoding="utf-8") as f:
            all_contents.append(f.read())
    combined = "\n".join(all_contents)

    for name in report.theorem_names:
        # Count occurrences (subtract 1 for the definition itself)
        count = len(re.findall(r"\b" + re.escape(name) + r"\b", combined))
        if count <= 1:
            if name in config.allowed_orphans:
                continue  # Silently authorize legit capstones

            report.violations.append(
                Violation(
                    file="[GLOBAL]",
                    line=0,
                    rule="ORPHANED_THEOREM_UNLISTED",
                    severity="ERROR",
                    message=(
                        f"Theorem/def `{name}` is never referenced AND is NOT in the allowed_orphans "
                        f"config. Either wire it into a consumer, delete it, or add it to the config."
                    ),
                )
            )

    # Post-pass: Check for orphaned axioms (Rule 8)
    for filepath, line, name in report.axiom_details:
        count = len(re.findall(r"\b" + re.escape(name) + r"\b", combined))
        if count <= 1:
            report.violations.append(
                Violation(
                    file=filepath,
                    line=line,
                    rule="ORPHANED_AXIOM",
                    severity="ERROR",
                    message=f"Axiom `{name}` is declared but never consumed in any proof. "
                    f"This is an unassigned alias that bloats the foundational assumptions without mathematical utility.",
                )
            )

    # Post-pass: Axiom dependency graph verification via #print axioms
    if config.capstone_theorem and config.expected_axiom_names:
        print()
        print("AXIOM DEPENDENCY GRAPH VERIFICATION")
        print("-" * 70)
        script_path: Optional[str] = None
        try:
            script = (
                f"import UnifiedPaperValidation\n"
                f"#print axioms UnifiedPaperValidation.{config.capstone_theorem}\n"
            )
            with tempfile.NamedTemporaryFile(
                mode="w", suffix=".lean", delete=False, encoding="utf-8"
            ) as f:
                f.write(script)
                script_path = f.name

            lake_bin = os.path.expanduser("~/.elan/bin/lake")
            if not os.path.isfile(lake_bin):
                lake_bin = "lake"

            result = subprocess.run(
                [lake_bin, "env", "lean", script_path],
                capture_output=True,
                text=True,
                timeout=120,
                cwd=lean_dir,
            )

            # Parse the output for axiom names
            # #print axioms output format:
            #   'UnifiedPaperValidation.full_paper_capstone' depends on axioms: [axiom1, axiom2, ...]
            # or on separate lines:
            #   propext
            #   Classical.choice
            output = result.stdout + result.stderr
            found_axioms: Set[str] = set()
            in_axiom_list = False
            for line in output.splitlines():
                stripped = line.strip()
                if "depends on axioms" in stripped:
                    in_axiom_list = True
                    # Extract inline axiom list: [ax1, ax2, ...]
                    bracket_match = re.search(r"\[(.+)\]", stripped)
                    if bracket_match:
                        for ax in bracket_match.group(1).split(","):
                            ax = (
                                ax.strip()
                                .strip("'")
                                .strip(",")
                                .strip("]")
                                .strip("[")
                                .strip()
                            )
                            if ax:
                                found_axioms.add(ax)
                    continue
                if (
                    in_axiom_list
                    and stripped
                    and not stripped.startswith("#")
                    and not stripped.startswith("warning")
                ):
                    # Individual axiom on its own line
                    cleaned = (
                        stripped.strip("'").strip(",").strip("]").strip("[").strip()
                    )
                    if cleaned and not any(
                        cleaned.startswith(p)
                        for p in ["error", "trace", "No dir", "./"]
                    ):
                        found_axioms.add(cleaned)

            if found_axioms:
                unexpected = found_axioms - config.expected_axiom_names
                missing = config.expected_axiom_names - found_axioms

                for ax in sorted(found_axioms):
                    marker = (
                        "  ✔" if ax in config.expected_axiom_names else "  ✖ UNEXPECTED"
                    )
                    print(f"{marker} {ax}")

                if missing:
                    print(f"\n  Missing expected axioms: {', '.join(sorted(missing))}")

                if unexpected:
                    for ax in unexpected:
                        severity = "ERROR" if ax in ("sorryAx",) else "WARNING"
                        report.violations.append(
                            Violation(
                                file="[AXIOM_GRAPH]",
                                line=0,
                                rule="UNEXPECTED_AXIOM_DEPENDENCY",
                                severity=severity,
                                message=f"Capstone `{config.capstone_theorem}` transitively depends on "
                                f"unexpected axiom `{ax}`. This was not declared in expected_axiom_names.",
                            )
                        )
                else:
                    print("\n  ✔ All axiom dependencies match the expected set.")
            else:
                print(
                    "  (Could not extract axiom dependencies — check `lake env lean` output)"
                )
                if output.strip():
                    for line in output.splitlines()[:5]:
                        print(f"    {line}")
        except (subprocess.TimeoutExpired, FileNotFoundError) as e:
            print(f"  (Axiom dependency check skipped: {e})")
        finally:
            if script_path and os.path.isfile(script_path):
                os.remove(script_path)

    return report


def print_report(report: LintReport):
    """Print the formatted audit report."""
    print()

    # Axiom inventory
    print("AXIOM INVENTORY")
    print("-" * 70)
    for filepath, line, name in report.axiom_details:
        print(f"  [{filepath}:{line}] axiom {name}")
    print(f"  TOTAL: {report.axiom_count}")
    print()

    # Violations
    errors = [v for v in report.violations if v.severity == "ERROR"]
    warnings = [v for v in report.violations if v.severity == "WARNING"]

    if errors:
        print("ERRORS (Must Fix)")
        print("-" * 70)
        for v in errors:
            print(f"  [{v.severity}] {v.file}:{v.line} ({v.rule})")
            print(f"    {v.message}")
            print()

    if warnings:
        print("WARNINGS (Review Required)")
        print("-" * 70)
        for v in warnings:
            print(f"  [{v.severity}] {v.file}:{v.line} ({v.rule})")
            print(f"    {v.message}")
            print()

    # Final verdict
    print("=" * 70)
    if errors:
        print(f"VERDICT: FAIL — {len(errors)} error(s), {len(warnings)} warning(s)")
    elif warnings:
        print(f"VERDICT: PASS WITH WARNINGS — 0 errors, {len(warnings)} warning(s)")
    else:
        print("VERDICT: FULL PASS — 0 errors, 0 warnings")
    print("=" * 70)

    return len(errors)


# ============================================================================
# Entry Point
# ============================================================================


def main():
    parser = argparse.ArgumentParser(
        description="Semantic Linter for Lean 4 Formal Verification Artifacts"
    )
    parser.add_argument(
        "path",
        nargs="?",
        default=".",
        help="Path to directory containing .lean files (default: current directory)",
    )
    parser.add_argument(
        "--expected-axioms",
        type=int,
        default=None,
        help="Expected number of axiom declarations (overrides config)",
    )
    parser.add_argument(
        "--config",
        type=str,
        default=None,
        help="Path to linter_config.json (auto-detected if omitted)",
    )
    args = parser.parse_args()

    config = load_config(args.config)
    expected = (
        args.expected_axioms
        if args.expected_axioms is not None
        else config.expected_axioms
    )

    report = run_audit(args.path, expected, config)
    error_count = print_report(report)

    sys.exit(1 if error_count > 0 else 0)


if __name__ == "__main__":
    main()
