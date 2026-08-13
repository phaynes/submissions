# Completed Design - PR2 `SandwichedRenyi.lean` Split

## Purpose

PR2 is a concept-boundary refactor of the `QuantumInfo` entropy layer. It
extracts the sandwiched Renyi relative entropy family from
`QuantumInfo/Entropy/Relative.lean` into a dedicated file while keeping the
Umegaki relative entropy API stable.

The design goal is not simply to reduce line count. The goal is to make the
mathematical ownership clearer:

- `D̃_α` and its analytic proof machinery belong to the sandwiched Renyi file.
- `qRelativeEnt`, notation `𝐃`, and Umegaki-facing theorems belong to
  `Relative.lean`.
- Facts at `α = 1` that are naturally about the sandwiched family should be
  proved once in the sandwiched file and reused by the Umegaki wrapper layer.

## Final Architecture

| File | Final role |
|---|---|
| `QuantumInfo.lean` | Publicly imports `QuantumInfo.Entropy.SandwichedRenyi` before `QuantumInfo.Entropy.Relative`. |
| `QuantumInfo/Entropy/SandwichedRenyi.lean` | Owns `SandwichedRelRentropy`, notation `D̃_`, sandwiched nonnegativity, additivity, congruence, continuity, alpha-equals-one lower-semicontinuity, and the supporting spectral/eigen-weight proof machinery. |
| `QuantumInfo/Entropy/Relative.lean` | Owns `qRelativeEnt`, notation `𝐃`, and Umegaki-facing wrappers/properties. |
| `scripts/LinterExemption.txt` | Adds the new sandwiched file to the same temporary style-lint exemption class as the moved QuantumInfo entropy code. |

## Key V2 Design Decision

The initial mechanical split exposed a bad boundary: `Relative.lean` still
needed internal eigen-weight helpers from the sandwiched analytic engine. Making
those helpers public would have solved the import problem, but it would have
made implementation details part of the public API.

The V2 design fixes the boundary instead:

1. Move the alpha-equals-one lower-semicontinuity proof into
   `SandwichedRenyi.lean`.
2. Expose the public boundary theorem
   `sandwichedRelRentropy_one_lowerSemicontinuous`.
3. Keep `qRelativeEnt.lowerSemicontinuous` in `Relative.lean` with the same
   public statement, implemented as:

   ```lean
   simpa [qRelativeEnt] using sandwichedRelRentropy_one_lowerSemicontinuous (ρ := ρ)
   ```

This keeps the eigen-weight helpers private while preserving the Umegaki theorem
surface.

## Proof Graph Method

The refactor was driven by Lean-backed facts rather than source scraping:

1. Capture a baseline of declarations, public statements, privacy, axiom
   dependencies, and elaborated kernel signatures.
2. Query Lean through the Varro-backed Lean query path for declaration
   placement, dependencies, type hashes, and private-name resolution.
3. Move the declarations that belong to the `D̃_α` concept into the new file.
4. Use the proof graph to detect the lower-semicontinuity boundary problem.
5. Apply the V2 correction above.
6. Validate the result with module builds, the PR2 harness, Varro equivalence
   evidence, Claude review, and full `lake build`.

The JSON files in `evidence/varro/` are evidence snapshots. The authority is the
reproducible Lean query path used to produce them.

## Public Surface Contract

Expected and observed public drift are recorded in
`evidence/varro/equivalence-report.json`.

The deliberate public change is:

- `sandwichedRelRentropy_one_lowerSemicontinuous` is exposed from
  `SandwichedRenyi.lean` as the boundary theorem used by the Umegaki wrapper.

The deliberate ownership change is:

- `inner_log_bounded_near` and `qRelativeEnt_lowerSemicontinuous_2` move from
  `Relative.lean` to `SandwichedRenyi.lean`.

The deliberate privacy restoration is:

- `eigenWeight`, `inner_cfc_eq_sum_eigenWeight`, `eigenWeight_nonneg`, and
  `eigenWeight_zero_of_eigenvalue_zero` resolve as private declarations inside
  `SandwichedRenyi.lean`.

## Standards Position

The PR is a large move of code that was already in the QuantumInfo style-lint
migration area. Direct style linting of the new file reports inherited issues
from the moved block, so the design adds `QuantumInfo/Entropy/SandwichedRenyi.lean`
to `scripts/LinterExemption.txt` rather than mixing style normalization into the
refactor. This is recorded in `evidence/standards-trace.md`.

## Out of Scope

This PR does not:

- rename existing declarations;
- proof-golf or style-normalize the moved block;
- relocate general `HermitianMat` lemmas to `ForMathlib`;
- split `SandwichedRenyi.lean` again;
- change any physics theorem statement.

Those are separate review topics. PR2 is the concept-boundary split plus the V2
proof-ownership correction needed to make the split sound.
