# PR#1 — Curved-surface measures (Cone, Torus, Ellipsoid)

The follow-on to the joint-convexity proof: a small family of curved-surface measure/
distribution constructions in `PhyslibAlpha/SpaceAndTime/Space/Surfaces/`. The intent
(per the operator) is to submit **all three shapes together** as one PR, so the reviewer
sees one coherent contribution rather than three separate small PRs.

> **Honest status.** Only **Cone** is written and compiling. **Torus** and **Ellipsoid**
> are **not yet written** — they are blocked on a design question the reviewer must rule
> on first (below), and are real Lean work to be done on a toolchain-equipped machine.
> Nothing here fabricates a proof that does not exist.

## Status of each surface

| Surface | State | Evidence |
|---|---|---|
| **Cone** | proved, compiling; **not yet committed** to a branch | [`Cone/proof/Cone.lean`](Cone/proof/Cone.lean) (full file), `.olean` present (48 KB, sha256 `ebe688d9…`) |
| **Torus** | **not written** — blocked on the measure-idiom ruling | [`Torus/PLAN.md`](Torus/PLAN.md) |
| **Ellipsoid** | **not written** — blocked on the same ruling | [`Ellipsoid/PLAN.md`](Ellipsoid/PLAN.md) |

## The design question that blocks Torus and Ellipsoid

The existing Surfaces idiom defines surface measures as **unweighted** pushforwards,
e.g. `Measure.map halfPlane (volume.restrict halfPlaneDomain)`. This coincides with the
intended surface measure when the parametrization is **area-preserving**; a cone is
handled with a **constant** slant factor (which is why `Cone` works cleanly today).

For **genuinely curved** surfaces (torus, ellipsoid) the area factor **varies with
position**, so the natural extension weights the parameter domain by the Jacobian first:

```
Measure.map φ ((volume.restrict D).withDensity J)      -- J = Jacobian / area factor
```

**The question for the reviewer:** is a Jacobian `withDensity` the idiomatic extension of
the Surfaces measure convention for curved surfaces, or is a different formulation
preferred? Torus and Ellipsoid should be *stated* according to this ruling, so writing
them before the ruling risks redoing them. This question is also surfaced to the reviewer
in the PR#0 packet (it is the one open judgement call there).

## Completing this PR

Torus and Ellipsoid are genuine formalization work requiring the Lean toolchain
(`lean4:v4.31.0`) and, ideally, the ruling above. The precise task is written up in
[`../../process/handoff-torus-ellipsoid.md`](../../process/handoff-torus-ellipsoid.md)
for a Lean-capable session to pick up: write each surface following the ruled idiom,
verify `#print axioms` (no `sorryAx`), and stage each here with the same treatment the
PR#0 proof received (excerpt + patch + evidence).

Once all three compile and are committed, this directory graduates from *plan* to a full
submission packet mirroring PR#0's structure.
