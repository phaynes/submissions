## Summary

Adds three PhyslibAlpha curved-surface measure/distribution modules:

- `Cone.lean`
- `Torus.lean`
- `Ellipsoid.lean`

`PhyslibAlpha.lean` imports all three surface modules.

## Implementation notes

Cone uses the existing graph-surface convention with the constant area factor
`sqrt (a ^ 2 + 1)`.

Torus and Ellipsoid use weighted parameter measures via `withDensity`, so the
position-dependent Jacobian factor is explicit before pushing the measure forward.
These are documented as parametrized surface measures; the files do not assert equality
with intrinsic Hausdorff measure.

The Torus parametrization intentionally does not claim global injectivity for all radius
parameters.

## Checks

- `lake build`
- `lake build PhyslibAlpha`
- `lake build PhyslibAlpha.SpaceAndTime.Space.Surfaces.Torus`
- `lake build PhyslibAlpha.SpaceAndTime.Space.Surfaces.Ellipsoid`
- `lake exe runPhyslibAlphaLinters`
- direct `./scripts/lint-style.py` on Cone/Torus/Ellipsoid
- `lake exe sorry_lint`
- `#print axioms` for Torus/Ellipsoid top-level definitions:
  `[propext, Classical.choice, Quot.sound]`
