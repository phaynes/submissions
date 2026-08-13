# Coding Standards Trace

This trace records how the PR2 refactor was checked against the standards that
apply to this repository.

## Sources

- `physlib-contrib/docs/ReviewGuidelines.md`
- `physlib-contrib/AGENTS.md`
- `physlib-contrib/AI-POLICY.md`
- `physlib-contrib/scripts/README.md`
- `physlib-contrib/scripts/lint-style.py`, adapted from Mathlib style linting

## Result

The PR conforms to the standards for a move/refactor PR, with one explicit
style-lint disclosure:

- `QuantumInfo/Entropy/SandwichedRenyi.lean` is a new tracked file but consists
  almost entirely of code moved out of `QuantumInfo/Entropy/Relative.lean`.
- `Relative.lean` is already listed in `scripts/LinterExemption.txt`.
- The moved code has inherited line-length, indentation, and semicolon style
  debt that predates this refactor.
- Fixing that debt inside the split PR would convert a concept-boundary move into
  a large proof-style rewrite, making statement-fidelity review harder.
- Therefore the new file is added to `scripts/LinterExemption.txt` and the PR
  packet discloses this explicitly.

This follows the current QuantumInfo lint migration pattern: exempt large legacy
files until they can be normalized deliberately, file by file.

## Checks

| Check | Status |
|---|---|
| No `sorry` introduced by refactor | PASS via PR2 harness and full build |
| No unreviewed statement drift | PASS via PR2 harness and Varro equivalence |
| No unreviewed privacy drift | PASS via PR2 harness and Varro private-name resolution |
| Import acyclicity | PASS via full build and Claude review |
| `scripts/LinterExemption.txt` updated for new moved file | PASS |
| `./scripts/lint-style.sh` | PASS in current checkout |
| `lake exe lint_all` | REPO-EXTERNAL FAIL; captured log reports unrelated `Physlib/...` style failures and no PR2 `QuantumInfo` file hits |
| Rendered documentation | PASS |

The direct file-level style linter reports inherited style issues if run on
`SandwichedRenyi.lean` alone. That is expected and is the reason for the
explicit exemption. The PR is therefore honest about style state while still
preserving the stronger semantic checks.

`lint-style.sh` lints tracked files from `git ls-files`; the new Lean file is
still untracked in this local preparation checkout. The packet therefore also
records `evidence/logs/lint-style-exemption-check.log`, which confirms the new
path is exactly listed in `scripts/LinterExemption.txt`. Once the PR files are
staged/tracked, the standard style gate will exclude the moved file under that
documented exemption.
