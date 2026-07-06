# Torus - implementation status

Status: implemented and compiling.

The torus contribution defines:

- `Space.TorusParameter`
- `Space.torus`
- `Space.torusDensity` / `Space.torusDensityNNReal`
- `Space.torusParameterMeasure`
- `Space.torusMeasure`
- `Space.torusDist`
- integral pullback lemmas through both the weighted parameter measure and the explicit
  density over the product circle measure

The measure is the pushforward of the product circle measure weighted by
`|r| * |R + r * v_0|`. This is intentionally a parametrized surface measure and does
not claim intrinsic Hausdorff-measure equality or global injectivity for all radius
parameters.

Source: `proof/Torus.lean`.
