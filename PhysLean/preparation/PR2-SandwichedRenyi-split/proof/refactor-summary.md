# Lean Refactor Summary

## Source Changes

The PR2 implementation changes the PhysLean checkout in four places:

| Path | Role |
|---|---|
| `QuantumInfo.lean` | Adds `public import QuantumInfo.Entropy.SandwichedRenyi` before `QuantumInfo.Entropy.Relative`. |
| `QuantumInfo/Entropy/SandwichedRenyi.lean` | New concept file for the sandwiched Renyi relative entropy family and its proof machinery. |
| `QuantumInfo/Entropy/Relative.lean` | Reduced Umegaki relative entropy file; keeps `qRelativeEnt` and delegates lower semicontinuity to the new sandwiched boundary theorem. |
| `scripts/LinterExemption.txt` | Adds the new file to the same style-lint migration boundary as the moved QuantumInfo entropy code. |

## Main Proof Ownership Change

The key proof refactor is:

- `sandwichedRelRentropy_one_lowerSemicontinuous` lives in
  `QuantumInfo/Entropy/SandwichedRenyi.lean`.
- `qRelativeEnt.lowerSemicontinuous` remains in
  `QuantumInfo/Entropy/Relative.lean` with the same public type, implemented by
  unfolding `qRelativeEnt = D̃_1`.

This keeps the Umegaki theorem stable while avoiding public exposure of
spectral/eigen-weight implementation helpers.

## Equivalence Evidence

Equivalence is recorded in:

- `evidence/varro/equivalence-report.json`
- `evidence/final-validation-report.md`
- `evidence/logs/pr2-harness.log`
- `evidence/logs/pr2-harness-axioms.log`

The final report confirms:

- public drift matches the reviewed expected drift;
- `qRelativeEnt.lowerSemicontinuous` has unchanged normalized type hash;
- eigen-weight helpers resolve as private declarations;
- affected modules and the full library build successfully.
