# SQT — conditional formal proof of the Stochastic-Quantum Correspondence thermodynamics

**Status: preparation / staging.** This directory stages the SQC (Stochastic-Quantum
Correspondence) thermodynamics proof for review, teaching, and eventual submission. It is
assembled from the working framework at
`mentormind/helios-projects/project/sqc-proof-framework` so that a reader — a reviewer, a
student, or a future maintainer — can follow the argument **step by step, and see exactly
what it does and does not assume**.

This is the *common overall packet*. Each individual proof module has its own detailed
subdirectory under [`proofs/`](proofs/); the shared framing, the honest axiom surface, and
the overall argument chain live here.

---

## 1. What is being proved, and how strong the claim is

The framework mechanizes, in Lean 4, key results of quantum thermodynamics under the
**Barandes Stochastic-Quantum Correspondence** (arXiv:2302.03852; Phys. Rev. A 109,
032206). The honest, defensible claim is **conditional**, not absolute:

> Assuming the **4 explicit Lean `axiom` declarations** listed in
> [`overview/axiom-surface.md`](overview/axiom-surface.md), the SQC thermodynamic proof
> modules compile with **no `sorry` and no `admit`**, **no known-false axiom is present**,
> and the product corollaries follow. This is a *conditional* proof artifact — it must
> **not** be described as an unconditional or axiom-free proof of quantum thermodynamics.

Two honesty points that this packet foregrounds rather than hides (they are the whole
reason it can "stand the highest scrutiny"):

- **It is conditional on 4 axioms.** Three are accepted paper-level physics assumptions
  (Stinespring dilation, strong subadditivity, Spohn entropy production); the axiom
  surface documents each with its citation and exactly what is being assumed.
- **Its history includes a *refuted* axiom.** An earlier independent audit (using the
  Fable model) found that a previously-assumed axiom, `relative_entropy_jointly_convex`,
  was **false unconditionally** (a `log 0 = 0` junk-value artifact), and it was rescoped
  to `support_le` with a kernel-verified refutation. This is disclosed deliberately: the
  process that produced this artifact actively hunts for and removes unsound assumptions,
  and that is a feature, not something to paper over.

## 2. The argument chain (module map)

The Lean development is 11 proof modules (~157 theorems/lemmas). A dependency-ordered
map — foundations → embedding → entropy → free energy → the SQC correspondence — is in
[`overview/proof-map.md`](overview/proof-map.md). In brief:

| Layer | Modules | Role |
|---|---|---|
| Foundations | `BasicDefinitions`, `MathsAxioms`, `PhyslibBridge` | density matrices, PSD/trace facts, bridge to the physics library |
| Embedding | `CPTPEmbedding`, `Correspondence` | CPTP maps, Stinespring, the stochastic-quantum embedding |
| Entropy | `PinchingEntropy` (2570 lines), `InformationTheory` | von Neumann entropy, SSA, pinching, channel capacity, Landauer |
| Thermodynamics | `CoherentFreeEnergy`, `MaxEntCanonical`, `ClassicalLimit` | free energy, canonical/Gibbs states, the classical limit |
| Target | `SQT_Axiom` | Spohn inequality and the SQC correspondence target |

The 4 axioms live in `PinchingEntropy` (1) and `SQT_Axiom` (3).

## 3. How this packet is organised

```
sqt/
├── README.md                 ← this file (the common overall packet)
├── overview/
│   ├── axiom-surface.md       ← the 4 axioms, each with citation + what is assumed
│   └── proof-map.md           ← dependency graph of the 11 modules → the SQC result
└── proofs/
    └── <Module>/              ← one per proof module (11 of them)
        ├── <Module>.source.lean  ← snapshot of the module as staged
        ├── status.md             ← what it proves, its axioms, build state
        └── fable-review.md        ← Fable's golf + soundness/axiom-reduction findings
        └── fable-refactor.diff    ← Fable's proposed refactor (see the review for its verification status)
```

## 4. The refactor pass (what Fable produced, and its trust level)

Each module's `fable-review.md` is a first-pass analysis by the **Fable** model with two
aims:

1. **Golf / legibility** — tighten proofs toward the clear, step-by-step form this packet
   is meant to have (fewer `have`s, better idiom, named intermediate steps where they aid
   reading).
2. **Soundness / axiom review** — look for axiom-reduction opportunities and, critically,
   any latent unsoundness (Fable's demonstrated strength on this codebase).

**Start with the synthesis:** [`proofs/SUMMARY.md`](proofs/SUMMARY.md) collates all 11
module reviews — the soundness findings (ranked; the Landauer hidden-assumption is the one
to fix first), the axiom-discharge plan, and the recommended order of work. The per-module
`fable-review.md` files have the detail.

**Trust level — read this before acting on any refactor proposal:** these are
*first-pass proposals*, not verified-and-merged changes. The framework builds on a
Mathlib-scale dependency tree where a full `lake build` is slow, so **not every proposal
was build-gated overnight**. Each `fable-review.md` states, per proposal, whether it was
compiled or is unverified. Treat unverified diffs as candidates to build-check tomorrow,
not as known-good. The soundness *observations* are valuable regardless of build state;
the *edits* must pass `cd verification/lean && lake build` before they are believed.

## 5. Verification of the underlying framework

- Build: `cd mentormind/helios-projects/project/sqc-proof-framework/verification/lean && lake build`
- Axiom/debt snapshot: `scripts/sqc_proof_debt_snapshot.sh` → expects `axioms=4`, `sorries_or_admits=0`
- Canonical axiom boundary (machine source of truth): `control/boundary.json`
- Toolchain: `leanprover/lean4:v4.31.0`

The per-module `status.md` records the build/axiom state for that module against this
boundary.
