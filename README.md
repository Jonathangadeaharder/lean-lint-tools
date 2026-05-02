# lean-lint-tools

Python linting tools for Lean 4 formal verification artifacts.

## Tools

### `semantic_linter.py`
Detects anti-patterns that pass the Lean 4 type-checker but constitute formal verification malpractice:
- Phantom variables, linter suppressions, dummy witnesses, sorry statements
- Axiom count mismatches, orphaned theorems, syntactic tautologies
- Tactic bloat, axiom dependency graph, paper theorem coverage

### `axiom_lint.py`
Regex-based linter for axiom/theorem reference validation. Checks axiom classifications, theorem-to-paper mappings, and derivation completeness.

## Usage

```bash
# Semantic linter
python semantic_linter.py [--expected-axioms N] [--config linter_config.json] [path/to/lean/files/]

# Axiom linter
python axiom_lint.py [--offline]
```

## Configuration

- `linter_config.json` — expected axioms, allowed orphans, wiring, capstone theorem
- `axiom_refs.json` — paper references, external/internal axiom classifications
- `paper_theorems.json` — paper theorem coverage tracking
