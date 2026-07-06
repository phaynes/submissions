# PR#1 - Curved-surface measures (Cone, Torus, Ellipsoid)

This package prepares a small PhyslibAlpha contribution under
`PhyslibAlpha/SpaceAndTime/Space/Surfaces/`.

## Status

| Surface | State | Source |
|---|---|---|
| Cone | Implemented and compiling | `Cone/proof/Cone.lean` |
| Torus | Implemented and compiling | `Torus/proof/Torus.lean` |
| Ellipsoid | Implemented and compiling | `Ellipsoid/proof/Ellipsoid.lean` |

All three are registered through `PhyslibAlpha.lean` in the working checkout.

Code commit: `db52bba8 feat(PhyslibAlpha): add curved surface measures`.

## Measure convention

Cone follows the existing graph-surface pattern with a constant slant factor:
`sqrt (a ^ 2 + 1)`.

Torus and Ellipsoid use the honest weighted-parameter-measure idiom:

```lean
Measure.map phi (parameterMeasure.withDensity jacobianDensity)
```

The files deliberately describe these as parametrized surface measures. They do not
assert equality with intrinsic Hausdorff measure. For Torus, no global injectivity claim
is made because the standard circular parametrization is not injective for all radius
choices.

## Included artifacts

- `proof/pr1-surfaces.patch` - patch for `PhyslibAlpha.lean`, `Cone.lean`, `Torus.lean`,
  and `Ellipsoid.lean`.
- `Cone/proof/Cone.lean` - current Cone source.
- `Torus/proof/Torus.lean` - current Torus source.
- `Ellipsoid/proof/Ellipsoid.lean` - current Ellipsoid source.
- `evidence/checks.md` - local verification evidence.
- `verify.sh` - verifier script to rerun the focused checks after applying the patch.

## Local verification summary

- `lake build PhyslibAlpha.SpaceAndTime.Space.Surfaces.Torus` passed.
- `lake build PhyslibAlpha.SpaceAndTime.Space.Surfaces.Ellipsoid` passed.
- `lake build PhyslibAlpha` passed.
- `lake build` passed; it reported one existing unused-simp warning outside this work.
- `lake exe runPhyslibAlphaLinters` passed.
- Direct Python style lint on Cone/Torus/Ellipsoid passed.
- `lake exe sorry_lint` passed.
- `#print axioms` for Torus/Ellipsoid top-level definitions showed only
  `[propext, Classical.choice, Quot.sound]`.

See `evidence/checks.md` for details and the known repo-wide style-lint caveat.
