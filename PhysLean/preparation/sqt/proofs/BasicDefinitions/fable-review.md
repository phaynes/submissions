# Fable review — `Proofs/BasicDefinitions.lean`

**Module:** 310 lines, 0 axioms (verified by grep and against `control/boundary.json`, whose
`per_module` lists only `PinchingEntropy` and `SQT_Axiom`).
**Reviewed:** 2026-07-08. Analysis only; no source edits.

## 1. What this module proves

This is the definitional foundation for the whole development. It supplies:

- **The core types** — `DensityMatrix n` (lines 25–29: Hermitian + PSD + trace-1 complex
  `Fin n × Fin n` matrix), `Hermitian n` (39–41), `UnitaryMatrix n` (44–46), plus the
  extensionality principle `DensityMatrix.matrix_ext` (34–36), which reduces equality of
  states to equality of their matrices via proof irrelevance.
- **The canonical constructions** — `pure_state` (168), `maximally_mixed` (183),
  `tensor_product` (220: Kronecker product reindexed along `finProdFinEquiv.symm`), and
  `partial_trace` (236: wraps `partialTrace₂` from `MathsAxioms`).
- **Well-formedness theorems** for each construction (Hermitian / PSD / trace-1 preservation,
  lines 52–141) — all fully proved; the enclosing `namespace Axioms` is historical naming only.
- **Spectral facts** — `eigenvalue_nonneg` (282) and `eigenvalue_le_one` (287): the spectrum
  of a state is a sub-probability vector.

Every downstream module (entropy, CPTP embedding, thermodynamics, the SQT target) states its
claims in terms of these types, so definitional fidelity here determines whether the
downstream theorems mean what they say.

## 2. Soundness review

**Finding: nothing unsound.** I checked each definition against the textbook object and each
theorem for vacuity, junk-value artifacts, and stub definitions. Details of what was checked:

- **`DensityMatrix` is the real object.** Hermitian, PSD (Mathlib `Matrix.PosSemidef` under
  `ComplexOrder`), trace 1. No stub fields, no `True` placeholders. `matrix_ext` is valid:
  the three non-matrix fields are `Prop`s, so proof irrelevance closes the constructor match.
  One redundancy, not a soundness issue: the pinned Mathlib defines `PosSemidef` as
  `M.IsHermitian ∧ …` (`.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean:59–60`),
  so the `hermitian` field is derivable as `ρ.positive.1`. Both are `Prop`s about the same
  matrix, so no inconsistency can be smuggled in — it is duplicate certification, nothing more.
- **`partial_trace` / `tensor_product` convention consistency — the critical check.**
  `partialTrace₂` (`MathsAxioms.lean:61–64`) is a genuine partial trace:
  `fun i j => ∑ k, ρ (finProdFinEquiv (i,k)) (finProdFinEquiv (j,k))` — same
  `finProdFinEquiv` convention (`(i,k) ↦ k + n·i`, second factor minor) that `tensor_product`
  uses for its reindex. Crucially, the roundtrip witness
  `partial_trace_tensor : partial_trace (tensor_product ρ τ) = ρ` is **proved** downstream
  (`CPTPEmbedding.lean:248–249`), which kernel-certifies the alignment. Without that witness,
  `partial_trace` would be pinned down only by Hermitian/PSD/trace-1 preservation — properties
  many wrong maps satisfy. The witness exists; the definition is honest.
- **`UnitaryMatrix` is one-sided** (`U * Uᴴ = 1`, line 46). For square matrices over a
  commutative ring this implies the other side (`mul_eq_one_comm`), and downstream code
  derives it exactly that way (`CPTPEmbedding.lean:419`). Mathematically adequate, not a
  weaker notion in disguise — but it deserves a one-line comment (see §4).
- **`pure_state`** (168): the outer-product convention `ψ i * star (ψ j)` is `|ψ⟩⟨ψ|`; PSD
  goes through Mathlib's `posSemidef_vecMulVec_self_star` (real lemma, `PosDef.lean:412`);
  the normalization hypothesis is genuinely used where it matters (`pure_state_normalized`,
  68–82). The `_h_norm` arguments to `pure_state_is_hermitian` (52) and
  `pure_state_is_possemidef` (60) are **unused** — vestigial, not vacuous: the conclusions
  hold without them and the hypothesis is satisfiable, so no claim is being silently weakened.
- **`maximally_mixed`** (183): guarded by `[NeZero n]`; the `(n:ℂ)⁻¹ · n = 1` step is proved
  with an explicit `n ≠ 0` (205–211). No junk-division exploit.
- **Spectral lemmas** (282–308): `eigenvalue_nonneg` comes from the PSD spectrum;
  `eigenvalue_le_one` really derives `∑ eigenvalues = 1` from the trace (via
  `hermitian_trace_eq_sum_eigs` and a `Complex.re` extraction) and applies
  `Finset.single_le_sum`. No junk values; the `ofReal`/`re` round trip is legitimate.
- **Degenerate dimensions:** `DensityMatrix 0` is uninhabited (empty trace is `0 ≠ 1`), so
  nothing in the module gains strength from vacuity.
- **No axiom declarations** despite `namespace Axioms` (49) — grep confirms zero `axiom`
  keywords, consistent with `boundary.json`.

## 3. Axiom-reduction opportunities

None — the module carries no axioms and rests only on Mathlib and the fully-proved
`MathsAxioms`. Implicit assumptions that could be tightened (all minor, all soundness-neutral):

- Drop the unused `_h_norm` hypotheses from `pure_state_is_hermitian` (52) and
  `pure_state_is_possemidef` (60); they narrow applicability for no gain.
- Resolve the `hermitian`/`positive` field redundancy in `DensityMatrix`: either remove the
  field in favour of a lemma `DensityMatrix.hermitian := ρ.positive.1` (touches many
  downstream field accesses, e.g. `PhyslibBridge.lean:77`) or keep it with a one-line comment
  acknowledging it is derivable. Given how worked-over the tree is, the comment is the
  cheaper honest option.
- `UnitaryMatrix` duplicates Mathlib's `Matrix.unitaryGroup`. Bespoke is defensible for
  teaching; if kept, state the two-sided companion lemma (`Uᴴ * U = 1`) next to the structure
  so readers see the one-sided field is not a weaker notion.

## 4. Legibility / teaching notes

Ranked by review impact:

1. **The `Axioms` namespace (49) and its stale header comment (48).** The comment still reads
   "Axioms for foundational properties to avoid heavy linear-algebra proofs" over a block of
   nine fully-proved theorems. A PhysLean reviewer grepping for the axiom surface will trip
   over `Quantum.Axioms.*` here and at the three call sites in `PinchingEntropy.lean`
   (67, 135, 337). Rename the namespace (e.g. `Foundations`) — the downstream refactor is
   three lines — rewrite the comment, and move the "Discharged (was an axiom)" history strings
   into the ledger, leaving plain mathematical docstrings. This is the single biggest
   reader-facing fix in the module.
2. **Extract `DensityMatrix.sum_eigenvalues_eq_one : ∑ i, ρ.eigenvalues i = 1` as a public
   lemma here.** The identical `ofReal`-sum / `Complex.re`-extraction block currently appears
   **four times**: inline in `eigenvalue_le_one` (289–302), twice inline in
   `PinchingEntropy.lean` (~66–79 and ~134–147), and once more as a *private* lemma
   `density_eigenvalues_sum_eq_one` (`PinchingEntropy.lean` ~334) that the other sites cannot
   see. One public lemma in `BasicDefinitions` kills all four copies and completes the natural
   teaching statement: the spectrum of a state is a probability vector (nonneg, sums to 1,
   each ≤ 1).
3. **Name the tensor matrix.** The expression
   `(Matrix.kronecker ρ₁.matrix ρ₂.matrix).submatrix finProdFinEquiv.symm finProdFinEquiv.symm`
   is written out four times (85–89, 98–101, 107–110, 222–224). A `def` (e.g. `tensorMatrix`)
   with the three field lemmas stated about the named form would make `tensor_product` read
   as one line per field. Add one sentence of prose fixing the index convention
   (`finProdFinEquiv (i,k) = k + n·i`, second factor minor) — it spares readers a Mathlib dig
   and explains at sight why `partialTrace₂` sums over `(i,k),(j,k)`.
4. **Small cleanups:** the `maximally_mixed` positivity proof spends ~10 lines (188–203) on a
   ℂ-smul → ℝ-smul cast dance that a small helper (PSD under a real-nonneg ℂ-scalar) would
   absorb; and `Hermitian.eq_conjTranspose` (249) / `Hermitian.conjTranspose_eq_self` (276)
   are each other's `.symm` — keep one.

## 5. Verdict

This module is in good shape: definitionally honest, zero axioms, no vacuous or junk-value
theorems, and — the point I probed hardest — its tensor-product and partial-trace conventions
are mutually consistent and kernel-certified by the downstream roundtrip
`partial_trace_tensor` (`CPTPEmbedding.lean:248`). There are **no soundness fixes to make**.
The highest-value follow-ups, all legibility: (1) rename the `Axioms` namespace and fix its
stale comment — trivial, and it removes the most likely reviewer misreading of the axiom
surface; (2) extract a public `sum_eigenvalues_eq_one`, deduplicating four copies of the same
argument across two modules and rounding out the spectrum-is-a-probability-vector story;
(3) name the Kronecker-reindex matrix and document the `finProdFinEquiv` index convention,
with the minor duplicate-lemma cleanups riding along.
