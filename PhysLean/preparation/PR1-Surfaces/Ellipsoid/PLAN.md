# Ellipsoid - implementation status

Status: implemented and compiling.

The ellipsoid contribution defines:

- `Space.EllipsoidParameter`
- `Space.ellipsoid`
- `Space.ellipsoidDensity` / `Space.ellipsoidDensityNNReal`
- `Space.ellipsoidParameterMeasure`
- `Space.ellipsoidMeasure`
- `Space.ellipsoidDist`
- integral pullback lemmas through both the weighted parameter measure and the explicit
  density over the unit-sphere measure

The measure is the pushforward of the unit-sphere measure weighted by
`|prod_i a_i| * sqrt (sum_i (u_i / a_i)^2)`. This is intentionally a parametrized
surface measure and does not claim intrinsic Hausdorff-measure equality.

Source: `proof/Ellipsoid.lean`.
