# lean-lint-tools

Python linting tools for Lean 4 formal verification artifacts.

## Tools

### `semantic_linter.py`
Detects anti-patterns that pass the Lean 4 type-checker but constitute formal verification malpractice:

| # | Rule | Severity |
|---|------|----------|
| 1 | Phantom variables — `_`-prefixed params in signatures | ERROR |
| 2 | Linter suppressions — `set_option linter.* false` / `#nolint` | ERROR |
| 3 | Dummy witnesses — hardcoded numeric witnesses in ∃ proofs | ERROR/WARNING |
| 4 | Sorry statements — `sorry` / `admit` / `sorryAx` | ERROR |
| 5 | Axiom count mismatch — expected vs actual axiom count | ERROR |
| 6 | Orphaned theorems — theorems never referenced elsewhere | ERROR |
| 7 | Syntactic tautologies — LHS = RHS prior to evaluation | ERROR |
| 7c | Vacuous ∃ positivity — `∃ c>0, expr>0` without parameter bound | ERROR |
| 7d | Unused named hypotheses — `h*` binders absent from proof body | ERROR |
| 8 | Tactic bloat — consecutive duplicate tactics, `skip` no-ops | ERROR/WARNING |
| 9 | Axiom dependency graph — transitive axiom verification via `#print axioms` | ERROR/WARNING |
| 10 | True conclusions — vacuous `True` conjuncts in capstone theorem | WARNING |
| 11 | Axiom provability — axioms classified as provable | WARNING |
| 12 | Disconnected theorems — expected theorem-to-theorem wiring missing | WARNING |
| 13 | Paper theorem coverage — manuscript-to-Lean coverage tracking | WARNING |

Additional checks (not in numbered list):
- **Tactic voids** — `intro _` / `rintro _` / `let _` discarding variables (ERROR)
- **Compiler trust** — `Lean.trustCompiler` bypassing kernel logic (ERROR)
- **Content discard** — `have _ :=` in capstone proofs discarding satellite results (WARNING)
- **Orphaned axioms** — declared but never consumed in any proof (ERROR)

### `axiom_lint.py`
Regex-based linter for Multiplicative Drift Analysis axiom/theorem reference validation. Checks axiom classifications (external vs internal), theorem-to-paper mappings, and derivation completeness (sorry detection).

## Usage

```bash
# Semantic linter
python semantic_linter.py [--expected-axioms N] [--config linter_config.json] [path/to/lean/files/]

# Axiom linter
python axiom_lint.py [--offline]
```

**Exit codes:** Both tools exit `0` on pass, `1` on any violation or error.

> **Note:** `axiom_lint.py` expects to run inside a parent project with a `FastEvolution/` directory containing `.lean` files and a `tools/axiom_refs.json` at the project root. It is not designed for standalone use outside that structure.

## Configuration

### `linter_config.json`
| Key | Type | Description |
|-----|------|-------------|
| `expected_axioms` | int | Expected number of axiom declarations |
| `allowed_orphans` | string[] | Theorem names exempt from orphan checks |
| `capstone_theorem` | string | Name of the capstone theorem for True-conclusion and axiom-graph checks |
| `capstone_true_threshold` | int | Max allowed vacuous `True` conjuncts in capstone (default 0) |
| `expected_axiom_names` | string[] | Expected transitive axiom dependencies for capstone |
| `axiom_classifications` | object | Axiom name → {status, difficulty, note, reference} map |
| `expected_wiring` | object[] | Required theorem-to-theorem connections [{from, to, status, note}] |
| `paper_theorems_path` | string | Path to `paper_theorems.json` (relative to config file) |

### `axiom_refs.json`
| Key | Type | Description |
|-----|------|-------------|
| `policy` | object | Linting policy flags (require structured contracts, locators, etc.) |
| `papers` | object | Paper ID → {title, url} map |
| `external_axioms` | object | External axiom name → {paper_id, locator} map |
| `internal_axioms` | object | Internal axiom name → {note} map |
| `theorems` | object | Theorem name → {paper_id} map |

### `paper_theorems.json`
Paper theorem coverage tracking. Contains `theorems` array (each with `paper_id`, `paper_name`, `lean_theorem`, `status`, `missing`, `gap_severity`) and optional `axiom_classifications` / `expected_wiring` overrides.
