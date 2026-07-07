# Fable review — `Proofs/Correspondence.lean` (185 lines, 0 axioms)

Reviewer: Fable 5 (analysis only, no source edits). Build re-verified: `lake build Proofs.Correspondence` green.
Context read: `PROOF_STATUS.md`, `axiom-surface.md`, `proof-map.md`, `control/boundary.json`, plus `SQT_Axiom.lean` and the `unitary_channel_bistochastic` region of `InformationTheory.lean` (needed to check this module's cross-references).

## 1. What this module proves

This is the concrete replacement for the retired abstract SQC existential (formerly `stochastic_quantum_theorem` in `SQT_Axiom.lean`, whose correspondence fields were `Nonempty`-placeholders). It provides:

- `StochasticDynamics n` (lines 32–38): a finite distribution `p0` (nonneg, sums to 1) and a column-stochastic transition matrix `Γ` (nonneg entries, `∀ j, ∑ i, Γ i j = 1`). Deliberately no Markov/semigroup law, preserving Barandes' indivisibility.
- `SQCorrespondence n D` (lines 43–46): a matrix `U` with `Uᴴ * U = 1` and the unistochastic matching `dyn_match : ∀ i j, D.Γ i j = Complex.normSq (U i j)` — the matching law is a data field, not a `Nonempty` wrapper.
- `corr_consistency` (lines 51–70): from unitarity + `dyn_match` alone (the proof never touches `D.Γ_stoch`), column-stochasticity of `Γ` is derived. This is the "interface has teeth" theorem.
- Two fully machine-checked instances: `swap` (NOT gate, lines 77–97) and `rot345` (a 3-4-5 real rotation, lines 154–180), each with an `example` re-deriving its column sums through `corr_consistency` (lines 100, 183).
- A negative example `not_unistochastic_example` (lines 106–112): the flat matrix `badΓ` is not the unistochastic image *of `Uswap`*.
- "Tier 1 instrument laws" (lines 116–146): diagonal-observable expectation agreement (`diagonal_observable_match`) and a diagonal one-step evolution match (`diagonal_evolution_match`).

Role in the DAG: leaf-adjacent. `SQT_Axiom.lean` imports it, but only references it in comments — no downstream theorem consumes `SQCorrespondence`. Its consumer is the acceptance gate (`sqc-proof-gate --require-instance SQCorrespondence`) and the writeup's A4 claim.

## 2. Soundness review

**No unsoundness found.** What I checked:

- **Instance verification (module-specific focus).** I re-derived every field of both instances by hand:
  - `swap`: `Uswap = !![0,1;1,0]` — `UᴴU = 1` ✓; `normSq` entries `{0,1}` match `Γswap` entrywise ✓; column sums 1 ✓; `p0swap = ![1,0]` normalized ✓.
  - `rot345`: columns `(3/5, 4/5)` and `(−4/5, 3/5)` are orthonormal ✓; `normSq` entries `9/25, 16/25` match `Γ345` entrywise ✓; column sums `9/25 + 16/25 = 1` ✓; `p0345 = ![3/5, 2/5]` sums to 1, nonneg ✓. It is genuinely non-permutation (entries strictly in `(0,1)`), so the "genuine superposition instance" claim (line 148) is fair.
  Both instances witness exactly what they claim.
- **`corr_consistency` is a genuine derivation, not circular.** `∑ i, D.Γ i j = 1` is also the structure field `D.Γ_stoch j`, so the theorem could have been "proved" trivially; the actual proof (lines 54–70) uses only `U_unitary` and `dyn_match` — `(UᴴU) j j = ∑ i normSq (U i j)`, then rewriting by the matching. Honest and correct. (Nuance: `Γ_stoch` remains a field of `StochasticDynamics`, so it is still assumed when *constructing* `D`; the theorem establishes redundancy given a correspondence, not removal of the field. The docstring "it is a theorem, not an independent assumption" is fair but this subtlety is worth a sentence — see §4.)
- **Vacuity / junk values.** No hypothesis class is empty (two instances inhabit the interface). No `log`, no division-by-zero channels; the only junk-value channel is the `.re` projection in `diagonalQuantumExpectation` (line 124), which is harmless here (all entries are real coercions) and honestly scoped by the name "diagonal".
- **One-sided unitarity.** `U_unitary : Uᴴ * U = 1` (line 45) is one-sided; in finite square dimension this implies the other side (`Matrix.mul_eq_one_comm`), so nothing is lost — but see Finding B.

Two findings, both statement-strength/claim-accuracy rather than falsity:

**Finding A (moderate): `quantumStepDiagonal` bakes in what its docstring claims is derived.** Lines 137–140 define `quantumStepDiagonal C i := ∑ j, Complex.normSq (C.U i j) * D.p0 j`, with docstring "The diagonal of the unitary evolution induced by the correspondence." That gloss is mathematically true — `(U · diag(p0) · Uᴴ) i i = ∑ j |U i j|² p0 j` — but it is asserted only in the docstring, never as a Lean lemma. Consequently `diagonal_evolution_match` (lines 143–146) reduces to a one-`simp` rewrite of `dyn_match`: nothing in the module connects the correspondence to actual unitary conjugation `U ρ Uᴴ`. A reviewer led by the names would believe the module proves an evolution law; it proves a re-indexing of the matching field. Contrast `diagonalQuantumExpectation` (lines 121–124), which *does* go through a real matrix trace and whose match theorem (127–131) therefore has content. Not unsound — nothing false is proved — but this is the exact "definition silently assumes what a downstream theorem should prove" pattern.

**Finding B (minor): the `unitary_channel_bistochastic` cross-reference overstates.** Lines 48–50 say "Upstream this is the axiom `unitary_channel_bistochastic`; here it is discharged." Checking `InformationTheory.lean:49–57`: the like-named theorem there is now proved, but its own docstring concedes that *as stated* it only re-asserts row-stochasticity (it reduces to the channel's `normalized` field, which comes from `U Uᴴ = 1`) and flags the column direction as "a framework weakness". `corr_consistency` proves precisely that missing *column* direction (from `Uᴴ U = 1`) — the complementary half, not a discharge of the same statement. Neither module proves two-sided bistochasticity from a single unitarity hypothesis. The docstring should say "supplies the column half flagged missing in `InformationTheory.unitary_channel_bistochastic`", or the module should prove the row side too (one `Matrix.mul_eq_one_comm` away) and claim bistochasticity honestly.

Two scope observations (not defects, should be stated where the module is presented):

- `SQCorrespondence` constrains only the *dynamics*. `D.p0` plays no role in the interface; there is no field tying the stochastic initial state to a quantum state. The Tier-1 laws adopt the diagonal-embedding convention (`ρ0 = diag(p0)`, observable `diag(f)`) inside their definitions rather than as a stated correspondence clause. The header's honesty ("the general Barandes reconstruction theorem remains future work", line 13) covers this, but the A4 claim in `axiom-surface.md` should be read as "dynamics-matching interface with checked instances", not a state-and-dynamics correspondence.
- The interface is disconnected from the framework's `DensityMatrix` machinery: `import Proofs.BasicDefinitions` (line 20) is apparently unused (nothing from it appears in the module), and no lemma states that `diag(p0)` is a `DensityMatrix`. The correspondence is currently a mathematical island reachable from the entropy/thermodynamics stack only by prose.

## 3. Axiom-reduction opportunities

No axioms in this module; boundary.json confirms. Tightening opportunities for the implicit assumptions:

1. **Bistochasticity, properly (fixes Finding B).** Add `corr_row_consistency : ∀ i, ∑ j, D.Γ i j = 1` proved via `Matrix.mul_eq_one_comm` (Mathlib) applied to `U_unitary`, then the row-sum computation already written inside `InformationTheory.unitary_to_channel.normalized`. This also lines up with Mathlib's `doublyStochastic` (`Mathlib.Analysis.Convex.Birkhoff` ecosystem): a corollary `C → D.Γ ∈ doublyStochastic ℝ (Fin n)` would anchor the interface to a standard Mathlib object and retire InformationTheory's flagged weakness in one move. What has to line up: Mathlib's `doublyStochastic` membership is stated via `∀ sums over rows and columns + nonneg`, all of which are available (`Γ_nonneg`, `Γ_stoch`, the new row lemma).
2. **The evolution lemma (fixes Finding A).** Prove `(C.U * Matrix.diagonal (fun j => (D.p0 j : ℂ)) * C.U.conjTranspose) i i = ((∑ j, Complex.normSq (C.U i j) * D.p0 j : ℝ) : ℂ)` — pure `Matrix.mul_apply` + `Complex.mul_conj` computation, no new imports — and redefine (or supplement) `quantumStepDiagonal` through it. Then `diagonal_evolution_match` states a real Born-rule evolution law.
3. **Bridge to `DensityMatrix`.** A lemma `diag(p0)` is a `DensityMatrix n` (Hermitian: real diagonal; PSD: nonneg diagonal; trace 1: `p0_sum`) would make the existing `BasicDefinitions` import earn its keep and let the entropy stack (e.g. `PinchingEntropy` results) apply to correspondence-embedded states — the first step toward `SQCorrespondence` being *consumed* by `SQT_Axiom` rather than cited in its comments.

## 4. Legibility / teaching notes

The module is short and already among the most readable in the DAG. Top improvements for a teaching/review audience:

1. **Extract the Born-normalization lemma.** The computation "columns of a unitary have unit `normSq` sum" is inlined in `corr_consistency` (lines 54–67), and its row twin is inlined in `InformationTheory.unitary_to_channel` (lines ~30–47). One named lemma (`sum_normSq_col_eq_one_of_unitary`, say) used in both places would shorten both proofs, teach the Born rule directly, and make the row/column symmetry visible instead of accidental.
2. **Clarify the negative example.** `not_unistochastic_example` (lines 106–112) refutes matching against `Uswap` *specifically*; `badΓ` is in fact unistochastic (any rotation with `cos²θ = 1/2`), and for `n = 2` *every* doubly stochastic matrix is unistochastic — a genuinely non-unistochastic doubly stochastic example first exists at `n = 3` (the classic `½(J − I)`). The section header's "for `Uswap`" qualifier is honest, but a two-line comment stating the above would prevent readers from taking the wrong lesson; formalizing the `n = 3` counterexample would give the interface a true negative certificate and is a nice self-contained exercise.
3. **Annotate the instance obligations.** The four `fin_cases <;> simp/norm_num` blocks (lines 91–97, 173–180) are ideal as machine checks but opaque as text. One comment per obligation ("columns orthonormal: 9/25 + 16/25 = 1", "entries squared: (−4/5)² = 16/25") turns them into worked examples. Also, `U345`'s anonymous-constructor literals `{ re := 3/5, im := 0 }` (lines 155–156) obscure that this is the real rotation with `cos θ = 3/5`; real coercions plus a one-line comment would read better.
4. **State the diagonal-embedding convention once.** The Tier-1 section (line 114) should open by saying: classical state ↦ `diag(p0)`, classical observable ↦ `diag(f)`; the laws below are the correspondence restricted to that embedding. And add a sentence to the `corr_consistency` docstring acknowledging that `Γ_stoch` remains a construction-time field — the theorem proves redundancy given a correspondence, not elimination of the field.

## 5. Verdict

The module is in good shape: zero axioms, both instances verify exactly what they claim (checked entrywise by hand and by rebuild), `corr_consistency` is a genuine non-circular derivation, and nothing false or vacuous is present — a clean result consistent with the post-campaign state. The highest-value follow-ups, ranked: **(1)** give `quantumStepDiagonal` real content by proving the `(U diag(p0) Uᴴ)ᵢᵢ` expansion lemma (Finding A — a statement-strength fix; do first, since the current `diagonal_evolution_match` reads as more than it is); **(2)** prove the row-stochastic companion and correct the `unitary_channel_bistochastic` cross-reference, ideally landing `Γ ∈ doublyStochastic` (Finding B — half soundness-of-claims, half integration; do second); **(3)** legibility polish per §4 — extract the Born-normalization lemma, clarify the `badΓ` example, annotate the instance checks (do later). A stretch goal that would move the whole framework: the `diag(p0) : DensityMatrix` bridge, so the correspondence stops being an island and `SQT_Axiom` can consume it in theorems rather than comments.
