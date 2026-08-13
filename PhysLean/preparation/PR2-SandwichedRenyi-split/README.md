# PhysLean PR2 Submission Brief - `SandwichedRenyi.lean` Split

This packet prepares a PhysLean pull request that extracts the sandwiched Renyi
relative entropy family from `QuantumInfo/Entropy/Relative.lean` into the new
concept file `QuantumInfo/Entropy/SandwichedRenyi.lean`.

The PR is a refactor, not a new theorem contribution. Its purpose is to make the
`QuantumInfo` entropy layer easier to review and extend after the accepted
Umegaki-relative-entropy work.

## Reviewer Summary

The original `Relative.lean` file mixed two concepts:

- the sandwiched Renyi family `D̃_α`, including its analytic engine, continuity,
  additivity, and alpha-equals-one limit machinery;
- the Umegaki quantum relative entropy `qRelativeEnt`, notation `𝐃`, and the
  theorems stated in the Umegaki vocabulary.

The refactor gives those concepts separate homes:

| File | Role after PR2 |
|---|---|
| `QuantumInfo/Entropy/SandwichedRenyi.lean` | Owns the `D̃_α` family, the spectral/eigen-weight proof machinery, additivity, continuity, congruence, and the alpha-equals-one lower-semicontinuity boundary theorem. |
| `QuantumInfo/Entropy/Relative.lean` | Owns `qRelativeEnt`, notation `𝐃`, and Umegaki-facing wrappers/properties. |

The important design point is that `qRelativeEnt` is definitionally `D̃_1`.
Therefore `Relative.lean` should import the sandwiched file and reuse the
alpha-family facts, rather than making the sandwiched file expose internals only
because `Relative.lean` needs them.

## What Changed

The final V2 refactor does the following.

- Adds `QuantumInfo/Entropy/SandwichedRenyi.lean`.
- Adds `public import QuantumInfo.Entropy.SandwichedRenyi` before
  `Relative.lean` in `QuantumInfo.lean`.
- Leaves `qRelativeEnt` and notation `𝐃` in `Relative.lean`.
- Moves the sandwiched Renyi definition, notation, additivity, continuity,
  congruence, nonnegativity, and supporting analytic proof machinery into the new
  file.
- Moves the alpha-equals-one lower-semicontinuity proof machinery into the new
  file and exposes the sandwiched boundary theorem
  `sandwichedRelRentropy_one_lowerSemicontinuous`.
- Keeps `qRelativeEnt.lowerSemicontinuous` public with the same statement; its
  proof is now the wrapper
  `simpa [qRelativeEnt] using sandwichedRelRentropy_one_lowerSemicontinuous`.
- Makes the eigen-weight implementation helpers private again:
  `eigenWeight`, `inner_cfc_eq_sum_eigenWeight`, `eigenWeight_nonneg`, and
  `eigenWeight_zero_of_eigenvalue_zero`.
- Adds `QuantumInfo/Entropy/SandwichedRenyi.lean` to
  `scripts/LinterExemption.txt`, matching the current QuantumInfo style-lint
  migration state. The file is a large move of currently exempt code; this PR is
  not a proof-golf or style-normalization PR.

## Methodology

The split was not done by line-number intuition.

1. A baseline was captured from the pre-refactor source.
2. Varro was bound to the Lean query binary and used to query declarations,
   modules, dependencies, and private-name resolution from Lean itself.
3. The proof graph showed that `qRelativeEnt.lowerSemicontinuous` depended on
   eigen-weight internals from the sandwiched analytic engine.
4. The ownership decision was changed accordingly: the alpha-equals-one
   lower-semicontinuity proof belongs with `D̃_α`, and `Relative.lean` should be
   a wrapper at `α = 1`.
5. Claude reviewed the V2 refactor before final equivalence checks.
6. Final validation compared V1 and V2 public surfaces, wrapper signatures,
   private helper resolution, harness output, and full Lean build output.

This is the core lesson for future Lean refactors: use Lean-backed facts as the
authority, and use JSON only as a transport/evidence format. Avoid source
scraping as the primary proof of correctness.

## Evidence

The packet includes the relevant evidence locally:

| Artifact | Purpose |
|---|---|
| [`evidence/final-validation-report.md`](evidence/final-validation-report.md) | Human-readable final validation summary. |
| [`evidence/varro/equivalence-report.json`](evidence/varro/equivalence-report.json) | Structured V1-to-V2 equivalence report. |
| [`evidence/review/claude-review.md`](evidence/review/claude-review.md) | Independent Claude review: no blocking findings. |
| [`evidence/logs/`](evidence/logs/) | Build, harness, and full-library logs. |
| [`harness/20_check.sh`](harness/20_check.sh) | PR2 inventory, signature, privacy, axiom, and diff-shape harness. |
| [`verify.sh`](verify.sh) | One-command replay for the submission checks. |
| [`process/SRS.md`](process/SRS.md) | Process and standards requirements for this PR. |
| [`process/traceability.md`](process/traceability.md) | Requirement-to-evidence trace. |

Final validation passed:

- `lake build QuantumInfo.Entropy.SandwichedRenyi`
- `lake build QuantumInfo.Entropy.Relative`
- `harness/20_check.sh`
- `harness/20_check.sh --axioms`
- full `lake build`
- `./scripts/lint-style.sh`
- documentation render and packet SRS trace

The full build has one pre-existing unrelated warning in
`Physlib/Electromagnetism/Kinematics/EMPotential.lean`.

The optional full-repository `lake exe lint_all` gate was attempted. It reports
unrelated pre-existing style failures in `Physlib/...` files and no PR2
`QuantumInfo` file hits; see `evidence/checks.md` and
`evidence/logs/lint-all.log`.

## Reviewer Map

Suggested review order:

1. `QuantumInfo.lean`: confirm the new file is imported before `Relative`.
2. `QuantumInfo/Entropy/SandwichedRenyi.lean`: skim the module boundary and the
   definitions/API moved from `Relative.lean`.
3. `QuantumInfo/Entropy/Relative.lean`: confirm the Umegaki API remains small and
   wrapper-oriented.
4. `qRelativeEnt.lowerSemicontinuous`: confirm the statement is unchanged and now
   delegates to the sandwiched alpha-equals-one theorem.
5. `scripts/LinterExemption.txt`: confirm the new file is exempted for the same
   reason as the existing QuantumInfo entropy files.
6. Run `./verify.sh /path/to/physlib`.

## Scope Limits

This PR deliberately does not:

- rename existing declarations;
- style-normalize the moved proof block;
- split the new large sandwiched file further;
- relocate general `HermitianMat` lemmas into `ForMathlib`;
- change any physics theorem statement.

Those are follow-up PRs. This PR is the concept-boundary split plus the proof
ownership correction needed to make that split sound and reviewer-readable.
