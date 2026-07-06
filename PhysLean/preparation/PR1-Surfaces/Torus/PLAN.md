# Torus — plan (NOT YET WRITTEN)

**Status: not written.** Blocked on the measure-idiom ruling (see [PR#1 README](../README.md)).

Target: a `torus` parametrization `Space 2 → Space 3` and its `torusMeasure` /
`torusDist`, mirroring `Cone.lean`, but with a **position-varying** area factor —
the torus surface element depends on the poloidal angle. Under the proposed idiom:

```
torusMeasure R r := Measure.map (torus R r) ((volume.restrict D).withDensity J)
```

with `J` the Jacobian of the standard `(θ, φ) ↦ ((R + r cos θ) …)` parametrization.

Declarations to provide (following the Cone template):
- `torus`, `torus_injective` (on the fundamental domain), `torus_continuous`,
  `torus_measurableEmbedding`
- `torusMeasure`, `torusDist`, and the integral-identity lemmas

Acceptance: compiles under `lake build`; `#print axioms` on the top-level results shows
no `sorryAx`. To be done on a Lean-equipped machine per
[`handoff-torus-ellipsoid.md`](../../process/handoff-torus-ellipsoid.md).
