# Handoff — write & verify Torus and Ellipsoid surface measures (PR#1)

For a session/agent running on a machine **with the Lean toolchain installed**. The
current staging session could not do this: it had no `lake`/`elan`, and writing
unverified Lean would violate the evidence-honesty rule this repository is built on.

## Goal
Write `Torus.lean` and `Ellipsoid.lean` in
`PhyslibAlpha/SpaceAndTime/Space/Surfaces/`, following the existing `Cone.lean` as the
template, so all three curved-surface measures compile and can be submitted together as
PhysLean PR#1.

## Environment (must match)
- Toolchain: `leanprover/lean4:v4.31.0` (a `physlib` checkout's `lean-toolchain` pins
  this; `elan` fetches it automatically). Mathlib `v4.31.0`, rev `fabf563a7c95`.
- Work in a `physlib` checkout on a fresh branch off the joint-convexity work.

## Precondition — the measure-idiom ruling
Torus and Ellipsoid have a **position-varying** area factor, unlike Cone (constant slant).
The proposed idiom weights the parameter domain by the Jacobian:
`Measure.map φ ((volume.restrict D).withDensity J)`.
**Confirm the reviewer's ruling** (is `withDensity` the idiomatic extension?) before
fixing the statements — it is the open question in the PR#0 packet. If the ruling is not
yet available, draft against the `withDensity` idiom but flag the statements as
provisional.

## Tasks
1. **Torus** — parametrization `torus R r : Space 2 → Space 3`, plus `torus_injective`
   (on the fundamental domain), `torus_continuous`, `torus_measurableEmbedding`,
   `torusMeasure`, `torusDist`, and the integral-identity lemmas — mirroring the Cone
   declarations (`cone`, `cone_injective`, …, `coneMeasure`, `coneDist`,
   `coneDist_apply_eq_*`). Use the ruled measure idiom with `J` the poloidal Jacobian.
2. **Ellipsoid** — the analogous set for an axis-scaled spherical parametrization.
3. For each: `lake build` green, and `#print axioms` on the top-level definitions/lemmas
   shows only `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**. No `sorry`.

## Staging the result (mirror PR#0)
For each surface, under `PhysLean/preparation/PR1-Surfaces/<Shape>/`:
- `proof/<Shape>.lean` — the file (or its added section as an excerpt) + a real
  `git show`/`git diff` patch once committed.
- `evidence/checks.md` — the four checks' results (statement, `#print axioms`, build, lint),
  captured from a real run.
- update `PR1-Surfaces/README.md` status table from "not written" → proved/compiling.
Replace each `PLAN.md` with the real material. Then the PR#1 packet matches the PR#0
structure and can be handed to a human to open the PR (human-only reviewer contact, per
AI-POLICY — see the repo README).

## Guardrails
- Do **not** mark a surface done without a real `#print axioms` run showing no `sorryAx`.
- Keep the statements consistent with the reviewer's ruling; if unruled, mark provisional.
- Evidence honesty is the whole point of this repo: never stage an unverified proof as
  verified.
