# Ellipsoid — plan (NOT YET WRITTEN)

**Status: not written.** Blocked on the same measure-idiom ruling as Torus.

Target: an `ellipsoid` parametrization and its `ellipsoidMeasure` / `ellipsoidDist`,
with a position-varying area factor (the ellipsoid surface element varies over the
sphere-like domain). Under the proposed idiom:

```
ellipsoidMeasure a b c := Measure.map (ellipsoid a b c) ((volume.restrict D).withDensity J)
```

`J` = Jacobian of the standard axis-scaled spherical parametrization.

Declarations to provide (following the Cone template): `ellipsoid`,
`ellipsoid_injective`, `ellipsoid_continuous`, `ellipsoid_measurableEmbedding`,
`ellipsoidMeasure`, `ellipsoidDist`, and integral-identity lemmas.

Acceptance: compiles; `#print axioms` shows no `sorryAx`. See
[`handoff-torus-ellipsoid.md`](../../process/handoff-torus-ellipsoid.md).
