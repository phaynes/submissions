# Proof map — module dependency graph

The 11 proof modules form a DAG (extracted from their `import Proofs.*` lines). Reading it
bottom-up gives the order in which the argument is built, and where the 4 axioms enter.

## Dependency edges (A ← B means "A imports B")

```
MathsAxioms            (root — no Proofs imports)
   ↑
BasicDefinitions ← MathsAxioms
   ↑
CPTPEmbedding ← BasicDefinitions, MathsAxioms
   ↑
PhyslibBridge ← BasicDefinitions, CPTPEmbedding, MathsAxioms
   ↑
PinchingEntropy ← PhyslibBridge, CPTPEmbedding, MathsAxioms          [1 axiom]
   ↑
ClassicalLimit ← PinchingEntropy
CoherentFreeEnergy ← PinchingEntropy, CPTPEmbedding
InformationTheory ← BasicDefinitions, PinchingEntropy, CPTPEmbedding, ClassicalLimit
MaxEntCanonical ← CoherentFreeEnergy
Correspondence ← BasicDefinitions
SQT_Axiom ← BasicDefinitions, PinchingEntropy, Correspondence        [3 axioms]
RelativeEntropyGibbs ← CoherentFreeEnergy   (3-line stub; not a real module)
```

## Layered reading (foundations → target)

1. **Foundations.** `MathsAxioms` (PSD/trace scalar facts) → `BasicDefinitions` (density
   matrices, quantum structures). No axioms.

2. **Embedding.** `CPTPEmbedding` (CPTP maps, Stinespring, the embedding theorem) and
   `PhyslibBridge` (interface to the physics library). `Correspondence` defines the
   stochastic-quantum correspondence structures. No axioms.

3. **Entropy — the analytic core.** `PinchingEntropy` (2570 lines, 46 theorems) carries
   von Neumann entropy, strong subadditivity, pinching, Araki–Lieb, monotonicity. **The 1
   entropy axiom** (`relative_entropy_jointly_convex`, on-support — Lieb's theorem) lives
   here. `InformationTheory` builds channel capacity / Landauer on top.

4. **Thermodynamics.** `CoherentFreeEnergy` (free energy, canonical states) →
   `MaxEntCanonical` (maximum-entropy / Gibbs) → `ClassicalLimit` (classical embedding
   agreement). No axioms.

5. **Target.** `SQT_Axiom` states the Spohn inequality and the SQC correspondence target.
   **The 3 remaining axioms** (`gkls_evolution`, `spohn_entropy_production`,
   `entropy_monotone_gkls`) enter here — the paper-level thermodynamic assumptions.

## Where the axioms concentrate

All 4 axioms are in exactly 2 modules — `PinchingEntropy` (1) and `SQT_Axiom` (3). Every
other module is unconditional given its imports. This is why axiom-reduction effort focuses
on those two: see [`axiom-surface.md`](axiom-surface.md) for each axiom and its discharge
path (notably, the PinchingEntropy axiom can be discharged against the PhysLean
`qRelativeEnt_joint_convexity` result once that PR merges).

## Refactor priority (for the Fable pass)

- **Highest value, hardest:** `PinchingEntropy` (2570 lines) — the analytic core; most to
  gain in legibility, but the slowest to build-verify.
- **High value:** `CPTPEmbedding` (566), `CoherentFreeEnergy` (489) — substantial, central.
- **Soundness focus:** `SQT_Axiom` — the axiom-carrying target; Fable's soundness review
  matters most here.
- **Quick wins:** the smaller foundation/bridge modules.
