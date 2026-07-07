import Proofs.PhyslibBridge
import Proofs.CPTPEmbedding
import Proofs.MathsAxioms
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.EReal.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Lagrange

/-!
# Entropy And Relative-Entropy Interface

Restart baseline for the entropy layer. The previous version mixed useful
statements with stale mathlib names, duplicate declarations, and incomplete
proof bodies. This file keeps the intended formal API buildable and records the
operator-theory obligations as explicit axioms for staged de-axiomatization.
-/

namespace Quantum

open Matrix Real
open scoped BigOperators ComplexOrder

/-- Eigenvalues of a density matrix lie in `[0,1]`. -/
lemma eigenvalue_mem_Icc {n : ℕ} (ρ : DensityMatrix n) (i : Fin n) :
    ρ.eigenvalues i ∈ Set.Icc 0 1 := by
  exact ⟨eigenvalue_nonneg ρ i, eigenvalue_le_one ρ i⟩

theorem mul_log_nonpos {x : ℝ} (h_pos : 0 < x) (h_le : x ≤ 1) :
    x * Real.log x ≤ 0 := by
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_pos) (Real.log_nonpos (le_of_lt h_pos) h_le)

theorem entropy_nonneg {n : ℕ} (ρ : DensityMatrix n) :
    0 ≤ von_neumann_entropy ρ := by
  rw [von_neumann_entropy]
  rw [Left.nonneg_neg_iff]
  apply Finset.sum_nonpos
  intro i _hi
  by_cases hzero : ρ.eigenvalues i = 0
  · simp [hzero]
  · have hpos : 0 < ρ.eigenvalues i :=
      lt_of_le_of_ne (eigenvalue_nonneg ρ i) (Ne.symm hzero)
    simpa [hzero] using mul_log_nonpos hpos (eigenvalue_le_one ρ i)

/-- Discharged (was an axiom) via the collaborative protocol (round 01): all three minds
    converged on inline Jensen; candidate authored by Codex GPT-5.5 (165s), kernel-verified. -/
theorem entropy_max_at_mixed {n : ℕ} (ρ : DensityMatrix n) :
    von_neumann_entropy ρ ≤ log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [von_neumann_entropy]
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hn
  have hentropy_eq : (∑ i : Fin n, Real.negMulLog (ρ.eigenvalues i)) = von_neumann_entropy ρ := by
    unfold von_neumann_entropy
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _hi => ?_
    by_cases hzero : ρ.eigenvalues i = 0
    · simp [hzero, Real.negMulLog_zero]
    · simp [hzero, Real.negMulLog_eq_neg]
  have h_sum_complex : ∑ j : Fin n, Complex.ofReal (ρ.eigenvalues j) = 1 := by
    have h_trace := Axioms.hermitian_trace_eq_sum_eigs ρ.toIsHermitian
    calc
      ∑ j : Fin n, Complex.ofReal (ρ.eigenvalues j) = ρ.matrix.trace := by
        simpa [DensityMatrix.eigenvalues] using h_trace.symm
      _ = 1 := ρ.normalized
  have h_nonneg : ∀ j, 0 ≤ ρ.eigenvalues j := fun j => eigenvalue_nonneg ρ j
  have h_sum_eq_one : ∑ j : Fin n, ρ.eigenvalues j = 1 := by
    have h_re : (∑ j : Fin n, Complex.ofReal (ρ.eigenvalues j)).re = 1 := by
      simpa using congrArg Complex.re h_sum_complex
    have : ∑ j : Fin n, ρ.eigenvalues j =
        (∑ j : Fin n, Complex.ofReal (ρ.eigenvalues j)).re := by
      simp
    linarith
  have hjensen :
      (∑ i : Fin n, (1 / (n : ℝ)) • Real.negMulLog ((n : ℝ) * ρ.eigenvalues i)) ≤
        Real.negMulLog (∑ i : Fin n, (1 / (n : ℝ)) • ((n : ℝ) * ρ.eigenvalues i)) := by
    refine Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
      (w := fun _ : Fin n => (1 : ℝ) / n) (p := fun i => (n : ℝ) * ρ.eigenvalues i) ?_ ?_ ?_
    · intro i _hi; positivity
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · intro i _hi
      have := h_nonneg i
      simp only [Set.mem_Ici]
      positivity
  simp only [smul_eq_mul] at hjensen
  have hsum_arg : (∑ i : Fin n, (1 / (n : ℝ)) * ((n : ℝ) * ρ.eigenvalues i)) = 1 := by
    have heq : ∀ i : Fin n, (1 / (n : ℝ)) * ((n : ℝ) * ρ.eigenvalues i) = ρ.eigenvalues i := fun i => by
      field_simp
    simp_rw [heq]
    exact h_sum_eq_one
  rw [hsum_arg, Real.negMulLog_one] at hjensen
  set C : ℝ := (1 / (n : ℝ)) * Real.negMulLog (n : ℝ) with hC
  have hexpand : ∀ i : Fin n,
      (1 / (n : ℝ)) * Real.negMulLog ((n : ℝ) * ρ.eigenvalues i)
        = ρ.eigenvalues i * C + Real.negMulLog (ρ.eigenvalues i) := by
    intro i
    rw [Real.negMulLog_mul (n : ℝ) (ρ.eigenvalues i), hC]
    field_simp
  simp_rw [hexpand] at hjensen
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, h_sum_eq_one, one_mul] at hjensen
  rw [hentropy_eq] at hjensen
  have hC_eq : C = - Real.log (n : ℝ) := by
    rw [hC, Real.negMulLog]
    field_simp
  rw [hC_eq] at hjensen
  linarith

/-- Discharged (was an axiom) — Sonnet 5 (501s, Phase A): a pure state ρ=|ψ⟩⟨ψ| has rank ≤ 1,
    so ≤ 1 nonzero eigenvalue; with trace 1 that eigenvalue is 1, the rest 0, giving entropy 0. -/
theorem entropy_pure_zero {n : ℕ} (ρ : DensityMatrix n)
    (h_pure : ∃ ψ : Fin n → ℂ,
      ρ.matrix = fun i j => ψ i * star (ψ j)) :
    von_neumann_entropy ρ = 0 := by
  classical
  obtain ⟨ψ, hψ⟩ := h_pure
  have hA : ρ.matrix.IsHermitian := ρ.toIsHermitian
  have hM : ρ.matrix = Matrix.vecMulVec ψ (star ψ) := by
    rw [hψ]; ext i j; simp [Matrix.vecMulVec_apply, Pi.star_apply]
  have hrank : ρ.matrix.rank ≤ 1 := by
    rw [hM]; exact Matrix.rank_vecMulVec_le ψ (star ψ)
  have hcard : Fintype.card {i : Fin n // hA.eigenvalues i ≠ 0} ≤ 1 := by
    rw [← hA.rank_eq_card_non_zero_eigs]; exact hrank
  have hsubsingleton : ∀ a b : {i : Fin n // hA.eigenvalues i ≠ 0}, a = b :=
    Fintype.card_le_one_iff.mp hcard
  have hsubsingleton' : ∀ a b : {i : Fin n // ρ.eigenvalues i ≠ 0}, a = b := by
    rw [DensityMatrix.eigenvalues_eq]; exact hsubsingleton
  have h_sum_complex : ∑ j : Fin n, Complex.ofReal (ρ.eigenvalues j) = 1 := by
    have h_trace := Axioms.hermitian_trace_eq_sum_eigs ρ.toIsHermitian
    calc
      ∑ j : Fin n, Complex.ofReal (ρ.eigenvalues j) = ρ.matrix.trace := by
        simpa [DensityMatrix.eigenvalues] using h_trace.symm
      _ = 1 := ρ.normalized
  have h_sum_eq_one : ∑ j : Fin n, ρ.eigenvalues j = 1 := by
    have h_re : (∑ j : Fin n, Complex.ofReal (ρ.eigenvalues j)).re = 1 := by
      simpa using congrArg Complex.re h_sum_complex
    have hcast : ∑ j : Fin n, ρ.eigenvalues j =
        (∑ j : Fin n, Complex.ofReal (ρ.eigenvalues j)).re := by
      simp
    linarith
  have hex : ∃ i0, ρ.eigenvalues i0 ≠ 0 := by
    by_contra h
    push Not at h
    have hsum0 : (∑ j : Fin n, ρ.eigenvalues j) = 0 := by simp [h]
    linarith
  obtain ⟨i0, hi0⟩ := hex
  have hzero_elsewhere : ∀ j : Fin n, j ≠ i0 → ρ.eigenvalues j = 0 := by
    intro j hj
    by_contra hjne
    have hEq := hsubsingleton' ⟨j, hjne⟩ ⟨i0, hi0⟩
    exact hj (congrArg Subtype.val hEq)
  have hsum_single : ∑ j : Fin n, ρ.eigenvalues j = ρ.eigenvalues i0 :=
    Finset.sum_eq_single i0 (fun j _ hj => hzero_elsewhere j hj)
      (fun h => absurd (Finset.mem_univ i0) h)
  have hi0_eq_one : ρ.eigenvalues i0 = 1 := by
    rw [← hsum_single]; exact h_sum_eq_one
  have hzero_or_one : ∀ i : Fin n, ρ.eigenvalues i = 0 ∨ ρ.eigenvalues i = 1 := by
    intro i
    by_cases hi : i = i0
    · subst hi; exact Or.inr hi0_eq_one
    · exact Or.inl (hzero_elsewhere i hi)
  unfold von_neumann_entropy
  rw [neg_eq_zero]
  apply Finset.sum_eq_zero
  intro i _hi
  rcases hzero_or_one i with h0 | h1
  · simp [h0]
  · simp [h1, Real.log_one]

/-! ## Fixed-basis pinching / dephasing -/

private lemma density_diag_nonneg {n : ℕ} (ρ : DensityMatrix n) (i : Fin n) :
    0 ≤ ρ.matrix i i := by
  exact Matrix.PosSemidef.diag_nonneg ρ.positive (i := i)

private lemma density_diag_eq_re {n : ℕ} (ρ : DensityMatrix n) (i : Fin n) :
    ((ρ.matrix i i).re : ℂ) = ρ.matrix i i := by
  have hstar : star (ρ.matrix i i) = ρ.matrix i i := by
    have h := congrFun (congrFun ρ.hermitian i) i
    simpa [Matrix.conjTranspose] using h
  apply Complex.ext
  · simp
  · simp
    have him := congrArg Complex.im hstar
    simp at him
    linarith

theorem pinching_matrix_hermitian {n : ℕ} (ρ : DensityMatrix n) :
    (Matrix.diagonal (fun i : Fin n => ρ.matrix i i)).conjTranspose =
      Matrix.diagonal (fun i : Fin n => ρ.matrix i i) := by
  rw [Matrix.diagonal_conjTranspose]
  apply Matrix.diagonal_eq_diagonal_iff.mpr
  intro i
  have h := congrFun (congrFun ρ.hermitian i) i
  simpa [Matrix.conjTranspose] using h

theorem pinching_matrix_posSemidef {n : ℕ} (ρ : DensityMatrix n) :
    IsPosSemidef (Matrix.diagonal (fun i : Fin n => ρ.matrix i i)) := by
  apply Matrix.PosSemidef.diagonal
  exact density_diag_nonneg ρ

theorem pinching_matrix_normalized {n : ℕ} (ρ : DensityMatrix n) :
    Matrix.trace (Matrix.diagonal (fun i : Fin n => ρ.matrix i i)) = 1 := by
  rw [Matrix.trace_diagonal]
  exact ρ.normalized

/-- Fixed-basis dephasing: keep exactly the diagonal entries of `ρ`. -/
noncomputable def pinching {n : ℕ} (ρ : DensityMatrix n) : DensityMatrix n :=
  { matrix := Matrix.diagonal (fun i : Fin n => ρ.matrix i i),
    hermitian := pinching_matrix_hermitian ρ,
    positive := pinching_matrix_posSemidef ρ,
    normalized := pinching_matrix_normalized ρ }

/-! ## Entropy inequalities -/

/-- Discharged (was an opaque axiom): the convex mixture pρ+(1-p)σ as a DensityMatrix.
    Construction by Codex GPT-5.5 (257s, design phase: all 4 fields + ℂ/ℝ smul-cast bridge). -/
noncomputable def density_matrix_mixture {n : ℕ} (ρ σ : DensityMatrix n) (p : ℝ)
    (h_p : 0 ≤ p ∧ p ≤ 1) : DensityMatrix n :=
  { matrix := (p : ℂ) • ρ.matrix + (((1 - p : ℝ) : ℂ)) • σ.matrix
    hermitian := by
      simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Complex.conj_ofReal,
        ρ.hermitian, σ.hermitian]
    positive := by
      have hp : 0 ≤ p := h_p.1
      have hq : 0 ≤ 1 - p := sub_nonneg.mpr h_p.2
      have hρ : Matrix.PosSemidef ((p : ℝ) • ρ.matrix) :=
        Matrix.PosSemidef.smul (x := ρ.matrix) (hx := ρ.positive) (a := p) hp
      have hσ : Matrix.PosSemidef ((1 - p : ℝ) • σ.matrix) :=
        Matrix.PosSemidef.smul (x := σ.matrix) (hx := σ.positive) (a := (1 - p : ℝ)) hq
      have hsum : Matrix.PosSemidef (((p : ℝ) • ρ.matrix) + ((1 - p : ℝ) • σ.matrix)) :=
        hρ.add hσ
      have hpcast : (p : ℂ) • ρ.matrix = (p : ℝ) • ρ.matrix := by
        ext i j
        simp [Algebra.smul_def]
      have hqcast : (((1 - p : ℝ) : ℂ)) • σ.matrix = ((1 - p : ℝ) • σ.matrix) := by
        ext i j
        simp [Algebra.smul_def]
      change Matrix.PosSemidef ((p : ℂ) • ρ.matrix + (((1 - p : ℝ) : ℂ)) • σ.matrix)
      rw [hpcast, hqcast]
      exact hsum
    normalized := by
      calc
        Matrix.trace ((p : ℂ) • ρ.matrix + (((1 - p : ℝ) : ℂ)) • σ.matrix)
            = (p : ℂ) * Matrix.trace ρ.matrix +
                (((1 - p : ℝ) : ℂ)) * Matrix.trace σ.matrix := by
              simp [Matrix.trace_add, Matrix.trace_smul]
        _ = (p : ℂ) * 1 + (((1 - p : ℝ) : ℂ)) * 1 := by
              rw [ρ.normalized, σ.normalized]
        _ = 1 := by
              norm_num }

-- `entropy_concave` is proved below, after `relative_entropy_real_nonneg_of_support` (Klein),
-- since the proof route goes via Klein's inequality applied to the mixture.

theorem entropy_subadditive {nA nB : ℕ} (ρ_AB : DensityMatrix (nA * nB)) :
    let ρ_A := partial_trace ρ_AB
    let ρ_B : DensityMatrix nB := partial_trace_A ρ_AB
    von_neumann_entropy ρ_AB ≤ von_neumann_entropy ρ_A + von_neumann_entropy ρ_B := by
  dsimp
  let σ := toMStatePair ρ_AB
  have h := Sᵥₙ_subadditivity σ
  dsimp [σ] at h
  rw [toMStatePair_traceRight] at h
  rw [toMStatePair_traceLeft] at h
  rw [← entropy_toMStatePair] at h
  rw [← entropy_toMState] at h
  rw [← entropy_toMState] at h
  exact h

/-! ## Relative entropy -/

/-- Support inclusion `supp ρ ≤ supp σ` (i.e. `ker σ ⊆ ker ρ`) — the finiteness condition for the
    quantum relative entropy. -/
noncomputable def support_le {n : ℕ} (ρ σ : DensityMatrix n) : Prop :=
  LinearMap.ker σ.matrix.mulVecLin ≤ LinearMap.ker ρ.matrix.mulVecLin

private lemma density_zero_diag_mulVec_single {n : ℕ} (ρ : DensityMatrix n) (i : Fin n)
    (hii : ρ.matrix i i = 0) :
    ρ.matrix *ᵥ Pi.single i (1 : ℂ) = 0 := by
  apply (ρ.positive.dotProduct_mulVec_zero_iff (Pi.single i (1 : ℂ))).mp
  rw [Matrix.mulVec_single_one]
  rw [← Pi.single_star, star_one]
  simp [hii]

theorem support_le_pinching {n : ℕ} (ρ : DensityMatrix n) :
    support_le ρ (pinching ρ) := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  ext j
  rw [Matrix.mulVec]
  apply Finset.sum_eq_zero
  intro i _hi
  have hvi_diag := congrFun hv i
  have hvi : ρ.matrix i i * v i = 0 := by
    simpa [pinching, Matrix.mulVec_diagonal] using hvi_diag
  by_cases hii : ρ.matrix i i = 0
  · have hcol := density_zero_diag_mulVec_single ρ i hii
    have hcolj := congrFun hcol j
    rw [Matrix.mulVec_single_one] at hcolj
    have hji : ρ.matrix j i = 0 := by simpa using hcolj
    simp [hji]
  · have hv_i : v i = 0 := (mul_eq_zero.mp hvi).resolve_left hii
    simp [hv_i]

/-- The finite real value `Tr(ρ (log ρ − log σ))`. Equals the true relative entropy only when
    `support_le ρ σ`; off support the junk `Real.log 0 = 0` drops the `+∞` penalty. -/
noncomputable def relative_entropy_real {n : ℕ} (ρ σ : DensityMatrix n) : ℝ :=
  (Matrix.trace (ρ.matrix * (matrix_log ρ.matrix - matrix_log σ.matrix))).re

/-- Quantum relative entropy — EReal-valued and support-aware: `+∞` off the support of σ. This
    REPLACES the former real-valued `relative_entropy`, whose companion `relative_entropy_nonneg`
    was a FALSE axiom (negative for singular σ, because `matrix_log` uses `Real.log 0 = 0`). -/
noncomputable def relative_entropy {n : ℕ} (ρ σ : DensityMatrix n) : EReal := by
  classical
  exact if support_le ρ σ then ((relative_entropy_real ρ σ : ℝ) : EReal) else ⊤

lemma relative_entropy_of_support {n : ℕ} {ρ σ : DensityMatrix n} (h : support_le ρ σ) :
    relative_entropy ρ σ = ((relative_entropy_real ρ σ : ℝ) : EReal) := by
  classical
  simp only [relative_entropy, h, if_true]

lemma relative_entropy_eq_top {n : ℕ} {ρ σ : DensityMatrix n} (h : ¬ support_le ρ σ) :
    relative_entropy ρ σ = ⊤ := by
  classical
  simp only [relative_entropy, h, if_false]

private lemma density_eigenvalues_sum_eq_one {n : ℕ} (ρ : DensityMatrix n) :
    ∑ i : Fin n, ρ.eigenvalues i = 1 := by
  have h_sum_complex : ∑ j : Fin n, Complex.ofReal (ρ.eigenvalues j) = 1 := by
    have h_trace := Axioms.hermitian_trace_eq_sum_eigs ρ.toIsHermitian
    calc
      ∑ j : Fin n, Complex.ofReal (ρ.eigenvalues j) = ρ.matrix.trace := by
        simpa [DensityMatrix.eigenvalues] using h_trace.symm
      _ = 1 := ρ.normalized
  have h_re : (∑ j : Fin n, Complex.ofReal (ρ.eigenvalues j)).re = 1 := by
    simpa using congrArg Complex.re h_sum_complex
  have h_cast : ∑ j : Fin n, ρ.eigenvalues j =
      (∑ j : Fin n, Complex.ofReal (ρ.eigenvalues j)).re := by
    simp
  linarith

private lemma density_log_diag {n : ℕ} (ρ : DensityMatrix n) :
    matrix_log ρ.matrix =
      (ρ.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.diagonal (fun i : Fin n => (Real.log (ρ.eigenvalues i) : ℂ)) *
        star (ρ.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
  rw [matrix_log, Matrix.IsHermitian.cfc_eq ρ.toIsHermitian Real.log]
  rfl

private lemma density_eigenvalue_diagonal {n : ℕ} (ρ : DensityMatrix n) :
    Matrix.diagonal (Complex.ofReal ∘ ρ.toIsHermitian.eigenvalues) =
      Matrix.diagonal (fun i : Fin n => (ρ.eigenvalues i : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal, DensityMatrix.eigenvalues, Function.comp_apply]
  · simp [Matrix.diagonal, hij]

private lemma density_spectral {n : ℕ} (ρ : DensityMatrix n) :
    ρ.matrix =
      (ρ.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.diagonal (fun i : Fin n => (ρ.eigenvalues i : ℂ)) *
        star (ρ.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
  simpa [DensityMatrix.eigenvalues, Matrix.mul_assoc, density_eigenvalue_diagonal ρ] using
    ρ.toIsHermitian.spectral_theorem

private lemma trace_unitaryGroup_conj {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace ((U : Matrix (Fin n) (Fin n) ℂ) * X *
        star (U : Matrix (Fin n) (Fin n) ℂ)) = Matrix.trace X := by
  calc
    Matrix.trace ((U : Matrix (Fin n) (Fin n) ℂ) * X *
        star (U : Matrix (Fin n) (Fin n) ℂ))
        = Matrix.trace (star (U : Matrix (Fin n) (Fin n) ℂ) *
            ((U : Matrix (Fin n) (Fin n) ℂ) * X)) := by
          rw [Matrix.trace_mul_comm]
    _ = Matrix.trace X := by
          rw [← Matrix.mul_assoc]
          rw [Unitary.coe_star_mul_self]
          rw [one_mul]

private lemma trace_self_log_eq_sum {n : ℕ} (ρ : DensityMatrix n) :
    (Matrix.trace (ρ.matrix * matrix_log ρ.matrix)).re =
      ∑ i : Fin n, ρ.eigenvalues i * Real.log (ρ.eigenvalues i) := by
  let U := ρ.toIsHermitian.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i : Fin n => (ρ.eigenvalues i : ℂ))
  let L : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i : Fin n => (Real.log (ρ.eigenvalues i) : ℂ))
  have hρ : ρ.matrix =
      (U : Matrix (Fin n) (Fin n) ℂ) * D * star (U : Matrix (Fin n) (Fin n) ℂ) := by
    simpa [U, D] using density_spectral ρ
  have hlog : matrix_log ρ.matrix =
      (U : Matrix (Fin n) (Fin n) ℂ) * L * star (U : Matrix (Fin n) (Fin n) ℂ) := by
    simpa [U, L] using density_log_diag ρ
  have htrace : Matrix.trace (ρ.matrix * matrix_log ρ.matrix) = Matrix.trace (D * L) := by
    calc
      Matrix.trace (ρ.matrix * matrix_log ρ.matrix)
          = Matrix.trace (((U : Matrix (Fin n) (Fin n) ℂ) * D *
              star (U : Matrix (Fin n) (Fin n) ℂ)) *
              ((U : Matrix (Fin n) (Fin n) ℂ) * L *
                star (U : Matrix (Fin n) (Fin n) ℂ))) := by
              rw [hlog, hρ]
      _ = Matrix.trace ((U : Matrix (Fin n) (Fin n) ℂ) * (D * L) *
              star (U : Matrix (Fin n) (Fin n) ℂ)) := by
              simp only [Matrix.mul_assoc]
              rw [← Matrix.mul_assoc (star (U : Matrix (Fin n) (Fin n) ℂ))
                (U : Matrix (Fin n) (Fin n) ℂ) (L * star (U : Matrix (Fin n) (Fin n) ℂ))]
              rw [Unitary.coe_star_mul_self]
              simp only [one_mul]
      _ = Matrix.trace (D * L) := trace_unitaryGroup_conj U (D * L)
  calc
    (Matrix.trace (ρ.matrix * matrix_log ρ.matrix)).re = (Matrix.trace (D * L)).re := by
      rw [htrace]
    _ = (Matrix.trace (Matrix.diagonal
          (fun i : Fin n => (ρ.eigenvalues i : ℂ) *
            (Real.log (ρ.eigenvalues i) : ℂ)))).re := by
          congr 1
          dsimp [D, L]
          rw [Matrix.diagonal_mul_diagonal]
    _ = (∑ i : Fin n, (ρ.eigenvalues i : ℂ) *
          (Real.log (ρ.eigenvalues i) : ℂ)).re := by
          rw [Matrix.trace_diagonal]
    _ = ∑ i : Fin n, ρ.eigenvalues i * Real.log (ρ.eigenvalues i) := by
          simp

private lemma trace_self_log_eq_neg_entropy {n : ℕ} (ρ : DensityMatrix n) :
    (Matrix.trace (ρ.matrix * matrix_log ρ.matrix)).re = -von_neumann_entropy ρ := by
  rw [trace_self_log_eq_sum ρ]
  unfold von_neumann_entropy
  rw [neg_neg]
  refine Finset.sum_congr rfl fun i _hi => ?_
  by_cases hzero : ρ.eigenvalues i = 0
  · simp [hzero]
  · simp [hzero]

private lemma aeval_diagonal_eq_diagonal_eval {n : ℕ} (d : Fin n → ℝ) (q : Polynomial ℝ) :
    Polynomial.aeval (Matrix.diagonal (fun i : Fin n => (d i : ℂ))) q =
      Matrix.diagonal (fun i : Fin n => ((Polynomial.eval (d i) q : ℝ) : ℂ)) := by
  induction q using Polynomial.induction_on with
  | C r =>
      ext i j
      by_cases h : i = j
      · subst h
        simp [Matrix.algebraMap_matrix_apply]
      · simp [Matrix.algebraMap_matrix_apply, h]
  | add p q hp hq =>
      rw [map_add, hp, hq]
      ext i j
      by_cases h : i = j
      · subst h
        simp
      · simp [Matrix.diagonal_apply_ne _ h]
  | monomial n r _hr =>
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, Matrix.diagonal_pow,
        Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h
        simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      · simp [Matrix.diagonal_apply_ne _ h]

private lemma matrix_log_real_diagonal {n : ℕ} (d : Fin n → ℝ) :
    matrix_log (Matrix.diagonal (fun i : Fin n => (d i : ℂ))) =
      Matrix.diagonal (fun i : Fin n => (Real.log (d i) : ℂ)) := by
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i : Fin n => (d i : ℂ))
  have hD : D.IsHermitian := by
    dsimp [D]
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    simp [isSelfAdjoint_iff]
  let s : Finset ℝ := (Finset.univ.image hD.eigenvalues) ∪ (Finset.univ.image d)
  let q : Polynomial ℝ := (Lagrange.interpolate s id) (fun x : ℝ => Real.log x)
  have hq_spec : (spectrum ℝ D).EqOn Real.log q.eval := by
    intro x hx
    have hxrange : x ∈ Set.range hD.eigenvalues := by
      simpa [hD.spectrum_real_eq_range_eigenvalues] using hx
    rcases hxrange with ⟨i, rfl⟩
    have hi : hD.eigenvalues i ∈ s := by
      dsimp [s]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    have hinterp := Lagrange.eval_interpolate_at_node (s := s) (v := id)
      (r := fun x : ℝ => Real.log x) (hvs := Set.injOn_id _) hi
    simpa [q] using hinterp.symm
  have hq_diag : ∀ i : Fin n, Polynomial.eval (d i) q = Real.log (d i) := by
    intro i
    have hi : d i ∈ s := by
      dsimp [s]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    have hinterp := Lagrange.eval_interpolate_at_node (s := s) (v := id)
      (r := fun x : ℝ => Real.log x) (hvs := Set.injOn_id _) hi
    simpa [q] using hinterp
  calc
    matrix_log (Matrix.diagonal (fun i : Fin n => (d i : ℂ))) = cfc Real.log D := by rfl
    _ = cfc q.eval D := by exact cfc_congr hq_spec
    _ = Polynomial.aeval D q := by exact cfc_polynomial q D (ha := hD)
    _ = Matrix.diagonal (fun i : Fin n => ((Polynomial.eval (d i) q : ℝ) : ℂ)) := by
          dsimp [D]
          rw [aeval_diagonal_eq_diagonal_eval]
    _ = Matrix.diagonal (fun i : Fin n => (Real.log (d i) : ℂ)) := by
          ext i j
          by_cases hij : i = j
          · subst hij
            simp [hq_diag]
          · simp [Matrix.diagonal_apply_ne _ hij]

private lemma trace_mul_diagonal_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) :
    Matrix.trace (A * Matrix.diagonal d) = ∑ i : Fin n, A i i * d i := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal]

private lemma trace_diagonal_mul_diagonal_eq {n : ℕ} (a d : Fin n → ℂ) :
    Matrix.trace (Matrix.diagonal a * Matrix.diagonal d) = ∑ i : Fin n, a i * d i := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]

private lemma pinching_matrix_eq_real_diagonal {n : ℕ} (ρ : DensityMatrix n) :
    (pinching ρ).matrix =
      Matrix.diagonal (fun i : Fin n => ((ρ.matrix i i).re : ℂ)) := by
  rw [pinching]
  exact (Matrix.diagonal_eq_diagonal_iff.mpr fun i => density_diag_eq_re ρ i).symm

private lemma trace_mul_log_pinching_eq {n : ℕ} (ρ : DensityMatrix n) :
    Matrix.trace (ρ.matrix * matrix_log (pinching ρ).matrix) =
      Matrix.trace ((pinching ρ).matrix * matrix_log (pinching ρ).matrix) := by
  let d : Fin n → ℝ := fun i => (ρ.matrix i i).re
  let logd : Fin n → ℂ := fun i => (Real.log (d i) : ℂ)
  have hpin_real : (pinching ρ).matrix = Matrix.diagonal (fun i : Fin n => (d i : ℂ)) := by
    simpa [d] using pinching_matrix_eq_real_diagonal ρ
  have hlog : matrix_log (pinching ρ).matrix = Matrix.diagonal logd := by
    rw [hpin_real]
    simpa [logd] using matrix_log_real_diagonal d
  calc
    Matrix.trace (ρ.matrix * matrix_log (pinching ρ).matrix)
        = Matrix.trace (ρ.matrix * Matrix.diagonal logd) := by rw [hlog]
    _ = ∑ i : Fin n, ρ.matrix i i * logd i := trace_mul_diagonal_eq ρ.matrix logd
    _ = Matrix.trace (Matrix.diagonal (fun i : Fin n => ρ.matrix i i) *
          Matrix.diagonal logd) := by
          rw [trace_diagonal_mul_diagonal_eq]
    _ = Matrix.trace ((pinching ρ).matrix * Matrix.diagonal logd) := by rfl
    _ = Matrix.trace ((pinching ρ).matrix * matrix_log (pinching ρ).matrix) := by rw [hlog]

/-- For the true fixed-basis dephasing, relative coherence is exactly entropy increase. -/
theorem relative_entropy_pinching_eq_entropy_diff {n : ℕ} (ρ : DensityMatrix n) :
    relative_entropy_real ρ (pinching ρ) =
      von_neumann_entropy (pinching ρ) - von_neumann_entropy ρ := by
  have hρ := trace_self_log_eq_neg_entropy ρ
  have hΔ := trace_self_log_eq_neg_entropy (pinching ρ)
  have hcross := congrArg Complex.re (trace_mul_log_pinching_eq ρ)
  unfold relative_entropy_real
  calc
    (Matrix.trace (ρ.matrix * (matrix_log ρ.matrix - matrix_log (pinching ρ).matrix))).re
        = (Matrix.trace (ρ.matrix * matrix_log ρ.matrix)).re -
            (Matrix.trace (ρ.matrix * matrix_log (pinching ρ).matrix)).re := by
            simp [Matrix.mul_sub, Matrix.trace_sub]
    _ = -von_neumann_entropy ρ -
            (Matrix.trace (ρ.matrix * matrix_log (pinching ρ).matrix)).re := by rw [hρ]
    _ = -von_neumann_entropy ρ -
            (Matrix.trace ((pinching ρ).matrix * matrix_log (pinching ρ).matrix)).re := by
            rw [hcross]
    _ = -von_neumann_entropy ρ - (-von_neumann_entropy (pinching ρ)) := by rw [hΔ]
    _ = von_neumann_entropy (pinching ρ) - von_neumann_entropy ρ := by ring

/-- Multiplying against the logarithm of a diagonal state only reads the diagonal of `ρ`. -/
theorem trace_mul_log_diagonal_eq_pinching {n : ℕ} (ρ τ : DensityMatrix n)
    (hτdiag : ∀ i j, i ≠ j → τ.matrix i j = 0) :
    Matrix.trace (ρ.matrix * matrix_log τ.matrix) =
      Matrix.trace ((pinching ρ).matrix * matrix_log τ.matrix) := by
  let d : Fin n → ℝ := fun i => (τ.matrix i i).re
  let logd : Fin n → ℂ := fun i => (Real.log (d i) : ℂ)
  have hτ_real : τ.matrix = Matrix.diagonal (fun i : Fin n => (d i : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [d, density_diag_eq_re τ i]
    · rw [hτdiag i j hij, Matrix.diagonal_apply_ne _ hij]
  have hlog : matrix_log τ.matrix = Matrix.diagonal logd := by
    rw [hτ_real]
    simpa [logd] using matrix_log_real_diagonal d
  calc
    Matrix.trace (ρ.matrix * matrix_log τ.matrix)
        = Matrix.trace (ρ.matrix * Matrix.diagonal logd) := by rw [hlog]
    _ = ∑ i : Fin n, ρ.matrix i i * logd i := trace_mul_diagonal_eq ρ.matrix logd
    _ = Matrix.trace (Matrix.diagonal (fun i : Fin n => ρ.matrix i i) *
          Matrix.diagonal logd) := by
          rw [trace_diagonal_mul_diagonal_eq]
    _ = Matrix.trace ((pinching ρ).matrix * Matrix.diagonal logd) := by rfl
    _ = Matrix.trace ((pinching ρ).matrix * matrix_log τ.matrix) := by rw [hlog]

/-- If `τ` is diagonal and `supp ρ ≤ supp τ`, then also `supp Δρ ≤ supp τ`. -/
theorem support_le_pinching_of_diagonal {n : ℕ} (ρ τ : DensityMatrix n)
    (hτdiag : ∀ i j, i ≠ j → τ.matrix i j = 0)
    (h : support_le ρ τ) :
    support_le (pinching ρ) τ := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  ext i
  have hτv_i : τ.matrix i i * v i = 0 := by
    have hentry := congrFun hv i
    have hrow : (τ.matrix *ᵥ v) i = τ.matrix i i * v i := by
      rw [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single i]
      · intro j _ hji
        rw [hτdiag i j (Ne.symm hji)]
        simp
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    rwa [hrow] at hentry
  show ((pinching ρ).matrix *ᵥ v) i = 0
  rw [pinching, Matrix.mulVec_diagonal]
  by_cases hτii : τ.matrix i i = 0
  · have hτsingle : τ.matrix *ᵥ Pi.single i (1 : ℂ) = 0 := by
      ext j
      rw [Matrix.mulVec_single_one]
      by_cases hji : j = i
      · subst hji
        exact hτii
      · exact hτdiag j i hji
    have hmem : Pi.single i (1 : ℂ) ∈ LinearMap.ker τ.matrix.mulVecLin := by
      simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hτsingle
    have hρsingle : ρ.matrix *ᵥ Pi.single i (1 : ℂ) = 0 := by
      simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using h hmem
    have hρii : ρ.matrix i i = 0 := by
      have hentry := congrFun hρsingle i
      rw [Matrix.mulVec_single_one] at hentry
      simpa using hentry
    simp [hρii]
  · have hvi : v i = 0 := (mul_eq_zero.mp hτv_i).resolve_left hτii
    simp [hvi]

/-- Pythagoras identity for fixed-basis pinching against a diagonal reference state. -/
theorem relative_entropy_pinching_add_of_diagonal {n : ℕ} (ρ τ : DensityMatrix n)
    (hτdiag : ∀ i j, i ≠ j → τ.matrix i j = 0) :
    relative_entropy_real ρ τ =
      relative_entropy_real ρ (pinching ρ) + relative_entropy_real (pinching ρ) τ := by
  let a := (Matrix.trace (ρ.matrix * matrix_log ρ.matrix)).re
  let b := (Matrix.trace (ρ.matrix * matrix_log (pinching ρ).matrix)).re
  let c := (Matrix.trace ((pinching ρ).matrix * matrix_log (pinching ρ).matrix)).re
  let e := (Matrix.trace (ρ.matrix * matrix_log τ.matrix)).re
  let f := (Matrix.trace ((pinching ρ).matrix * matrix_log τ.matrix)).re
  have hbc : b = c := by
    dsimp [b, c]
    exact congrArg Complex.re (trace_mul_log_pinching_eq ρ)
  have hef : e = f := by
    dsimp [e, f]
    exact congrArg Complex.re (trace_mul_log_diagonal_eq_pinching ρ τ hτdiag)
  have hρτ : relative_entropy_real ρ τ = a - e := by
    unfold relative_entropy_real
    dsimp [a, e]
    simp [Matrix.mul_sub, Matrix.trace_sub]
  have hρΔ : relative_entropy_real ρ (pinching ρ) = a - b := by
    unfold relative_entropy_real
    dsimp [a, b]
    simp [Matrix.mul_sub, Matrix.trace_sub]
  have hΔτ : relative_entropy_real (pinching ρ) τ = c - f := by
    unfold relative_entropy_real
    dsimp [c, f]
    simp [Matrix.mul_sub, Matrix.trace_sub]
  rw [hρτ, hρΔ, hΔτ, hbc, hef]
  ring

private lemma trace_diag_mul_mul_diag_mul_star_re {n : ℕ}
    (d l : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.trace
      (Matrix.diagonal (fun i : Fin n => (d i : ℂ)) * W *
        Matrix.diagonal (fun j : Fin n => (l j : ℂ)) * star W)).re =
      ∑ i : Fin n, ∑ j : Fin n, d i * Complex.normSq (W i j) * l j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal, Matrix.star_apply,
    Complex.normSq_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma trace_cross_log_eq_sum {n : ℕ} (ρ σ : DensityMatrix n) :
    (Matrix.trace (ρ.matrix * matrix_log σ.matrix)).re =
      ∑ i : Fin n, ∑ j : Fin n,
        ρ.eigenvalues i *
          Complex.normSq (((star
            (ρ.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) *
            (σ.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) i j) *
          Real.log (σ.eigenvalues j) := by
  let U := ρ.toIsHermitian.eigenvectorUnitary
  let V := σ.toIsHermitian.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i : Fin n => (ρ.eigenvalues i : ℂ))
  let L : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun j : Fin n => (Real.log (σ.eigenvalues j) : ℂ))
  let W : Matrix (Fin n) (Fin n) ℂ :=
    star (U : Matrix (Fin n) (Fin n) ℂ) * (V : Matrix (Fin n) (Fin n) ℂ)
  have hρ : ρ.matrix =
      (U : Matrix (Fin n) (Fin n) ℂ) * D * star (U : Matrix (Fin n) (Fin n) ℂ) := by
    simpa [U, D] using density_spectral ρ
  have hlogσ : matrix_log σ.matrix =
      (V : Matrix (Fin n) (Fin n) ℂ) * L * star (V : Matrix (Fin n) (Fin n) ℂ) := by
    simpa [V, L] using density_log_diag σ
  have hstarW : star W =
      star (V : Matrix (Fin n) (Fin n) ℂ) * (U : Matrix (Fin n) (Fin n) ℂ) := by
    dsimp [W]
    rw [StarMul.star_mul, star_star]
  have hUU : (U : Matrix (Fin n) (Fin n) ℂ) *
      star (U : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    (Matrix.mem_unitaryGroup_iff).mp U.2
  have halg :
      Matrix.trace (ρ.matrix * matrix_log σ.matrix) =
        Matrix.trace (D * W * L * star W) := by
    calc
      Matrix.trace (ρ.matrix * matrix_log σ.matrix)
          = Matrix.trace (((U : Matrix (Fin n) (Fin n) ℂ) * D *
              star (U : Matrix (Fin n) (Fin n) ℂ)) *
              ((V : Matrix (Fin n) (Fin n) ℂ) * L *
                star (V : Matrix (Fin n) (Fin n) ℂ))) := by
              rw [hlogσ, hρ]
      _ = Matrix.trace ((U : Matrix (Fin n) (Fin n) ℂ) * (D * W * L * star W) *
              star (U : Matrix (Fin n) (Fin n) ℂ)) := by
              rw [hstarW]
              dsimp [W]
              simp only [Matrix.mul_assoc]
              rw [hUU]
              simp only [mul_one]
      _ = Matrix.trace (D * W * L * star W) := trace_unitaryGroup_conj U (D * W * L * star W)
  rw [halg]
  simpa [D, L, W] using trace_diag_mul_mul_diag_mul_star_re
    (fun i : Fin n => ρ.eigenvalues i) (fun j : Fin n => Real.log (σ.eigenvalues j)) W

private lemma row_normSq_sum_of_mul_star {n : ℕ}
    {W : Matrix (Fin n) (Fin n) ℂ}
    (hW : W * star W = 1) (i : Fin n) :
    ∑ j : Fin n, Complex.normSq (W i j) = 1 := by
  have hentry : (W * star W) i i = (1 : Matrix (Fin n) (Fin n) ℂ) i i := by
    rw [hW]
  rw [Matrix.mul_apply] at hentry
  simp [Matrix.star_apply, Complex.mul_conj] at hentry
  have hre := congrArg Complex.re hentry
  simpa using hre

private lemma col_normSq_sum_of_star_mul {n : ℕ}
    {W : Matrix (Fin n) (Fin n) ℂ}
    (hW : star W * W = 1) (j : Fin n) :
    ∑ i : Fin n, Complex.normSq (W i j) = 1 := by
  have hentry : (star W * W) j j = (1 : Matrix (Fin n) (Fin n) ℂ) j j := by
    rw [hW]
  rw [Matrix.mul_apply] at hentry
  simp [Matrix.star_apply] at hentry
  have hre := congrArg Complex.re hentry
  simpa [Complex.normSq_apply] using hre

private lemma overlap_mul_star {n : ℕ}
    (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    let W : Matrix (Fin n) (Fin n) ℂ :=
      star (U : Matrix (Fin n) (Fin n) ℂ) * (V : Matrix (Fin n) (Fin n) ℂ)
    W * star W = 1 := by
  intro W
  have hVV : (V : Matrix (Fin n) (Fin n) ℂ) *
      star (V : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    (Matrix.mem_unitaryGroup_iff).mp V.2
  have hUstarU : star (U : Matrix (Fin n) (Fin n) ℂ) *
      (U : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    rw [Unitary.coe_star_mul_self]
  dsimp [W]
  rw [StarMul.star_mul, star_star]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (V : Matrix (Fin n) (Fin n) ℂ)
    (star (V : Matrix (Fin n) (Fin n) ℂ)) (U : Matrix (Fin n) (Fin n) ℂ)]
  rw [hVV]
  simp only [one_mul]
  exact hUstarU

private lemma overlap_star_mul {n : ℕ}
    (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    let W : Matrix (Fin n) (Fin n) ℂ :=
      star (U : Matrix (Fin n) (Fin n) ℂ) * (V : Matrix (Fin n) (Fin n) ℂ)
    star W * W = 1 := by
  intro W
  have hVstarV : star (V : Matrix (Fin n) (Fin n) ℂ) *
      (V : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    rw [Unitary.coe_star_mul_self]
  have hUU : (U : Matrix (Fin n) (Fin n) ℂ) *
      star (U : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    (Matrix.mem_unitaryGroup_iff).mp U.2
  dsimp [W]
  rw [StarMul.star_mul, star_star]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U : Matrix (Fin n) (Fin n) ℂ)
    (star (U : Matrix (Fin n) (Fin n) ℂ)) (V : Matrix (Fin n) (Fin n) ℂ)]
  rw [hUU]
  simp only [one_mul]
  exact hVstarV

private lemma overlap_row_sum {n : ℕ} (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (i : Fin n) :
    ∑ j : Fin n,
      Complex.normSq ((star (U : Matrix (Fin n) (Fin n) ℂ) *
        (V : Matrix (Fin n) (Fin n) ℂ)) i j) = 1 := by
  exact row_normSq_sum_of_mul_star (overlap_mul_star U V) i

private lemma overlap_col_sum {n : ℕ} (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (j : Fin n) :
    ∑ i : Fin n,
      Complex.normSq ((star (U : Matrix (Fin n) (Fin n) ℂ) *
        (V : Matrix (Fin n) (Fin n) ℂ)) i j) = 1 := by
  exact col_normSq_sum_of_star_mul (overlap_star_mul U V) j

private lemma support_zero_eigen_overlap_mul_eq_zero {n : ℕ}
    (ρ σ : DensityMatrix n) (h : support_le ρ σ) (i j : Fin n)
    (hq : σ.eigenvalues j = 0) :
    (ρ.eigenvalues i : ℂ) *
      (((star (ρ.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) *
        (σ.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) i j) = 0 := by
  let U := ρ.toIsHermitian.eigenvectorUnitary
  let V := σ.toIsHermitian.eigenvectorUnitary
  let W : Matrix (Fin n) (Fin n) ℂ :=
    star (U : Matrix (Fin n) (Fin n) ℂ) * (V : Matrix (Fin n) (Fin n) ℂ)
  let vσ : Fin n → ℂ := ⇑(σ.toIsHermitian.eigenvectorBasis j)
  have hq' : σ.toIsHermitian.eigenvalues j = 0 := by
    simpa [DensityMatrix.eigenvalues] using hq
  have hvσzero : σ.matrix *ᵥ vσ = 0 := by
    have hv := σ.toIsHermitian.mulVec_eigenvectorBasis j
    simpa [vσ, hq'] using hv
  have hvσmem : vσ ∈ LinearMap.ker σ.matrix.mulVecLin := by
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hvσzero
  have hvρmem : vσ ∈ LinearMap.ker ρ.matrix.mulVecLin := h hvσmem
  have hvρzero : ρ.matrix *ᵥ vσ = 0 := by
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hvρmem
  let x : Fin n → ℂ := star (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ vσ
  have hUU : (U : Matrix (Fin n) (Fin n) ℂ) *
      star (U : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    (Matrix.mem_unitaryGroup_iff).mp U.2
  have hUx : (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ x = vσ := by
    dsimp [x]
    rw [Matrix.mulVec_mulVec]
    rw [hUU]
    simp
  have hdiag :
      star (U : Matrix (Fin n) (Fin n) ℂ) * ρ.matrix *
          (U : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal (fun k : Fin n => (ρ.eigenvalues k : ℂ)) := by
    simpa [U, DensityMatrix.eigenvalues, Matrix.mul_assoc, density_eigenvalue_diagonal ρ] using
        ρ.toIsHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hDzero : Matrix.diagonal (fun k : Fin n => (ρ.eigenvalues k : ℂ)) *ᵥ x = 0 := by
    rw [← hdiag]
    calc
      (star (U : Matrix (Fin n) (Fin n) ℂ) * ρ.matrix *
          (U : Matrix (Fin n) (Fin n) ℂ)) *ᵥ x
          = star (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ
              (ρ.matrix *ᵥ ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ x)) := by
              simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = star (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ (ρ.matrix *ᵥ vσ) := by
              rw [hUx]
      _ = 0 := by simp [hvρzero]
  have hx_col : x = W *ᵥ Pi.single j (1 : ℂ) := by
    dsimp [x, W, vσ]
    rw [← σ.toIsHermitian.eigenvectorUnitary_mulVec j]
    rw [Matrix.mulVec_mulVec]
  have hx_apply : x i = W i j := by
    rw [hx_col, Matrix.mulVec_single_one]
    rfl
  have hcomp := congr_fun hDzero i
  simp [Matrix.mulVec_diagonal, hx_apply] at hcomp
  simpa [U, V, W] using hcomp

private lemma real_mul_normSq_eq_zero_of_ofReal_mul_eq_zero
    {p : ℝ} {z : ℂ} (h : (p : ℂ) * z = 0) :
    p * Complex.normSq z = 0 := by
  rcases mul_eq_zero.mp h with hp | hz
  · have hp' : p = 0 := Complex.ofReal_eq_zero.mp hp
    simp [hp']
  · have hz' : Complex.normSq z = 0 := Complex.normSq_eq_zero.mpr hz
    simp [hz']

private lemma weighted_log_le_log_weighted_of_zero_weight {n : ℕ}
    (w q : Fin n → ℝ)
    (hw_nonneg : ∀ j, 0 ≤ w j)
    (hw_sum : ∑ j : Fin n, w j = 1)
    (hq_nonneg : ∀ j, 0 ≤ q j)
    (hzero : ∀ j, q j = 0 → w j = 0) :
    ∑ j : Fin n, w j * Real.log (q j) ≤ Real.log (∑ j : Fin n, w j * q j) := by
  classical
  let t : Finset (Fin n) := Finset.univ.filter fun j => 0 < q j
  have hpos_of_w_ne : ∀ j : Fin n, w j ≠ 0 → 0 < q j := by
    intro j hwne
    exact lt_of_le_of_ne (hq_nonneg j) (fun hq0 => hwne (hzero j hq0.symm))
  have hw_sum_t : ∑ j ∈ t, w j = 1 := by
    have hfilter : ∑ j ∈ t, w j = ∑ j : Fin n, w j := by
      dsimp [t]
      exact Finset.sum_filter_of_ne (s := Finset.univ) (f := w)
        (p := fun j => 0 < q j) (by intro j _ hj; exact hpos_of_w_ne j hj)
    rw [hfilter, hw_sum]
  have hlog_filter :
      ∑ j ∈ t, w j * Real.log (q j) = ∑ j : Fin n, w j * Real.log (q j) := by
    dsimp [t]
    exact Finset.sum_filter_of_ne (s := Finset.univ) (f := fun j => w j * Real.log (q j))
      (p := fun j => 0 < q j) (by
        intro j _ hj
        have hwne : w j ≠ 0 := by
          intro hw0
          exact hj (by simp [hw0])
        exact hpos_of_w_ne j hwne)
  have hq_filter :
      ∑ j ∈ t, w j * q j = ∑ j : Fin n, w j * q j := by
    dsimp [t]
    exact Finset.sum_filter_of_ne (s := Finset.univ) (f := fun j => w j * q j)
      (p := fun j => 0 < q j) (by
        intro j _ hj
        by_contra hqpos
        have hq0 : q j = 0 := le_antisymm (le_of_not_gt hqpos) (hq_nonneg j)
        exact hj (by simp [hq0]))
  have hjensen :
      (∑ j ∈ t, w j • Real.log (q j)) ≤
        Real.log (∑ j ∈ t, w j • q j) := by
    refine strictConcaveOn_log_Ioi.concaveOn.le_map_sum
      (t := t) (w := w) (p := q) ?_ hw_sum_t ?_
    · intro j _; exact hw_nonneg j
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
  simpa [smul_eq_mul, hlog_filter, hq_filter] using hjensen

/-- Equality case of `weighted_log_le_log_weighted_of_zero_weight`: if the weighted-Jensen bound
    is tight, every `q j` with nonzero weight equals the weighted mean (the strict concavity of
    `log` on `Ioi 0` forces the points to coincide). -/
private lemma weighted_log_eq_weighted_of_zero_weight {n : ℕ}
    (w q : Fin n → ℝ)
    (hw_nonneg : ∀ j, 0 ≤ w j)
    (hw_sum : ∑ j : Fin n, w j = 1)
    (hq_nonneg : ∀ j, 0 ≤ q j)
    (hzero : ∀ j, q j = 0 → w j = 0)
    (heq : ∑ j : Fin n, w j * Real.log (q j) = Real.log (∑ j : Fin n, w j * q j)) :
    ∀ j : Fin n, w j ≠ 0 → q j = ∑ j : Fin n, w j * q j := by
  classical
  let t : Finset (Fin n) := Finset.univ.filter fun j => 0 < q j
  have hpos_of_w_ne : ∀ j : Fin n, w j ≠ 0 → 0 < q j := by
    intro j hwne
    exact lt_of_le_of_ne (hq_nonneg j) (fun hq0 => hwne (hzero j hq0.symm))
  have hw_sum_t : ∑ j ∈ t, w j = 1 := by
    have hfilter : ∑ j ∈ t, w j = ∑ j : Fin n, w j := by
      dsimp [t]
      exact Finset.sum_filter_of_ne (s := Finset.univ) (f := w)
        (p := fun j => 0 < q j) (by intro j _ hj; exact hpos_of_w_ne j hj)
    rw [hfilter, hw_sum]
  have hlog_filter :
      ∑ j ∈ t, w j * Real.log (q j) = ∑ j : Fin n, w j * Real.log (q j) := by
    dsimp [t]
    exact Finset.sum_filter_of_ne (s := Finset.univ) (f := fun j => w j * Real.log (q j))
      (p := fun j => 0 < q j) (by
        intro j _ hj
        have hwne : w j ≠ 0 := by
          intro hw0
          exact hj (by simp [hw0])
        exact hpos_of_w_ne j hwne)
  have hq_filter :
      ∑ j ∈ t, w j * q j = ∑ j : Fin n, w j * q j := by
    dsimp [t]
    exact Finset.sum_filter_of_ne (s := Finset.univ) (f := fun j => w j * q j)
      (p := fun j => 0 < q j) (by
        intro j _ hj
        by_contra hqpos
        have hq0 : q j = 0 := le_antisymm (le_of_not_gt hqpos) (hq_nonneg j)
        exact hj (by simp [hq0]))
  have heq_t : Real.log (∑ j ∈ t, w j • q j) = ∑ j ∈ t, w j • Real.log (q j) := by
    simp only [smul_eq_mul, hlog_filter, hq_filter]
    exact heq.symm
  have hiff := strictConcaveOn_log_Ioi.map_sum_eq_iff' (t := t) (w := w) (p := q)
    (fun j _ => hw_nonneg j) hw_sum_t (fun j hj => (Finset.mem_filter.mp hj).2)
  have hall := hiff.mp heq_t
  intro j hwj
  have hjt : j ∈ t := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hpos_of_w_ne j hwj⟩
  have := hall j hjt hwj
  simpa [smul_eq_mul, hq_filter] using this

private lemma finite_gibbs_nonneg {n : ℕ}
    (p r : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hr_nonneg : ∀ i, 0 ≤ r i)
    (hp_sum : ∑ i : Fin n, p i = 1)
    (hr_sum : ∑ i : Fin n, r i = 1)
    (hr_pos_of_hp_pos : ∀ i, 0 < p i → 0 < r i) :
    0 ≤ (∑ i : Fin n, p i * Real.log (p i)) -
      (∑ i : Fin n, p i * Real.log (r i)) := by
  have hterm : ∀ i : Fin n,
      p i * Real.log (r i) - p i * Real.log (p i) ≤ r i - p i := by
    intro i
    by_cases hp0 : p i = 0
    · have hr0 : 0 ≤ r i := hr_nonneg i
      simp [hp0, hr0]
    · have hp_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hp0)
      have hr_pos : 0 < r i := hr_pos_of_hp_pos i hp_pos
      have hlog : Real.log (r i / p i) ≤ r i / p i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hr_pos hp_pos)
      have hmul := mul_le_mul_of_nonneg_left hlog hp_pos.le
      calc
        p i * Real.log (r i) - p i * Real.log (p i)
            = p i * Real.log (r i / p i) := by
                rw [Real.log_div hr_pos.ne' hp_pos.ne']
                ring
        _ ≤ p i * (r i / p i - 1) := hmul
        _ = r i - p i := by
                field_simp [hp_pos.ne']
  have hsum :
      (∑ i : Fin n, (p i * Real.log (r i) - p i * Real.log (p i))) ≤
        ∑ i : Fin n, (r i - p i) := by
    exact Finset.sum_le_sum (by intro i _; exact hterm i)
  have hright : (∑ i : Fin n, (r i - p i)) = 0 := by
    rw [Finset.sum_sub_distrib, hr_sum, hp_sum, sub_self]
  rw [hright] at hsum
  rw [Finset.sum_sub_distrib] at hsum
  linarith

/-- Equality case of `finite_gibbs_nonneg`: if the Gibbs bound is exactly tight, `r = p`
    pointwise (the equality case of `log x ≤ x - 1`, applied term by term). -/
private lemma finite_gibbs_eq_zero {n : ℕ}
    (p r : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hr_nonneg : ∀ i, 0 ≤ r i)
    (hp_sum : ∑ i : Fin n, p i = 1)
    (hr_sum : ∑ i : Fin n, r i = 1)
    (hr_pos_of_hp_pos : ∀ i, 0 < p i → 0 < r i)
    (heq : (∑ i : Fin n, p i * Real.log (p i)) - (∑ i : Fin n, p i * Real.log (r i)) = 0) :
    ∀ i, r i = p i := by
  have hterm : ∀ i : Fin n,
      p i * Real.log (r i) - p i * Real.log (p i) ≤ r i - p i := by
    intro i
    by_cases hp0 : p i = 0
    · have hr0 : 0 ≤ r i := hr_nonneg i
      simp [hp0, hr0]
    · have hp_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hp0)
      have hr_pos : 0 < r i := hr_pos_of_hp_pos i hp_pos
      have hlog : Real.log (r i / p i) ≤ r i / p i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hr_pos hp_pos)
      have hmul := mul_le_mul_of_nonneg_left hlog hp_pos.le
      calc
        p i * Real.log (r i) - p i * Real.log (p i)
            = p i * Real.log (r i / p i) := by
                rw [Real.log_div hr_pos.ne' hp_pos.ne']
                ring
        _ ≤ p i * (r i / p i - 1) := hmul
        _ = r i - p i := by
                field_simp [hp_pos.ne']
  have hright : (∑ i : Fin n, (r i - p i)) = 0 := by
    rw [Finset.sum_sub_distrib, hr_sum, hp_sum, sub_self]
  have hslack_sum :
      ∑ i : Fin n, ((r i - p i) - (p i * Real.log (r i) - p i * Real.log (p i))) = 0 := by
    rw [Finset.sum_sub_distrib, hright, Finset.sum_sub_distrib]
    linarith [heq]
  have hslack_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ (r i - p i) - (p i * Real.log (r i) - p i * Real.log (p i)) := by
    intro i _; linarith [hterm i]
  have hslack_zero := (Finset.sum_eq_zero_iff_of_nonneg hslack_nonneg).mp hslack_sum
  intro i
  have hzero := hslack_zero i (Finset.mem_univ i)
  by_cases hp0 : p i = 0
  · have : r i = 0 := by simpa [hp0] using hzero
    simp [hp0, this]
  · have hp_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hp0)
    have hr_pos : 0 < r i := hr_pos_of_hp_pos i hp_pos
    have hstep3 : r i - p i = p i * Real.log (r i / p i) := by
      rw [Real.log_div hr_pos.ne' hp_pos.ne']
      linarith [hzero]
    have hcancel : p i * Real.log (r i / p i) = p i * (r i / p i - 1) := by
      rw [← hstep3]; field_simp
    have hxeq : Real.log (r i / p i) = r i / p i - 1 :=
      mul_left_cancel₀ hp_pos.ne' hcancel
    have hx1 : r i / p i = 1 := by
      by_contra hne
      have hlt := Real.log_lt_sub_one_of_pos (div_pos hr_pos hp_pos) hne
      linarith [hxeq]
    exact (div_eq_one_iff_eq hp_pos.ne').mp hx1

/-- Finite-branch Klein (the remaining honest gap): the real relative entropy is nonnegative on
    full support. TRUE — provable via diagonalization + doubly-stochastic overlap + Jensen
    (~250–350 LOC, scheduled). Kept as an EXPLICITLY SCOPED axiom: its `support_le` hypothesis keeps
    the gap visible, rather than laundering it back into an unconditional (false) claim. -/
theorem relative_entropy_real_nonneg_of_support {n : ℕ} (ρ σ : DensityMatrix n)
    (h : support_le ρ σ) : 0 ≤ relative_entropy_real ρ σ := by
  classical
  let U := ρ.toIsHermitian.eigenvectorUnitary
  let V := σ.toIsHermitian.eigenvectorUnitary
  let W : Matrix (Fin n) (Fin n) ℂ :=
    star (U : Matrix (Fin n) (Fin n) ℂ) * (V : Matrix (Fin n) (Fin n) ℂ)
  let P : Fin n → Fin n → ℝ := fun i j => Complex.normSq (W i j)
  let p : Fin n → ℝ := ρ.eigenvalues
  let q : Fin n → ℝ := σ.eigenvalues
  let r : Fin n → ℝ := fun i => ∑ j : Fin n, P i j * q j
  have hp_nonneg : ∀ i, 0 ≤ p i := by intro i; exact eigenvalue_nonneg ρ i
  have hq_nonneg : ∀ j, 0 ≤ q j := by intro j; exact eigenvalue_nonneg σ j
  have hp_sum : ∑ i : Fin n, p i = 1 := by
    simpa [p] using density_eigenvalues_sum_eq_one ρ
  have hq_sum : ∑ j : Fin n, q j = 1 := by
    simpa [q] using density_eigenvalues_sum_eq_one σ
  have hP_nonneg : ∀ i j, 0 ≤ P i j := by intro i j; exact Complex.normSq_nonneg _
  have hrow : ∀ i, ∑ j : Fin n, P i j = 1 := by
    intro i
    simpa [P, W, U, V] using overlap_row_sum U V i
  have hcol : ∀ j, ∑ i : Fin n, P i j = 1 := by
    intro j
    simpa [P, W, U, V] using overlap_col_sum U V j
  have hsupport_zero : ∀ i j, q j = 0 → p i * P i j = 0 := by
    intro i j hq0
    have hc := support_zero_eigen_overlap_mul_eq_zero ρ σ h i j (by simpa [q] using hq0)
    simpa [p, P, W, U, V] using real_mul_normSq_eq_zero_of_ofReal_mul_eq_zero hc
  have hr_nonneg : ∀ i, 0 ≤ r i := by
    intro i
    dsimp [r]
    exact Finset.sum_nonneg (by intro j _; exact mul_nonneg (hP_nonneg i j) (hq_nonneg j))
  have hr_sum : ∑ i : Fin n, r i = 1 := by
    calc
      ∑ i : Fin n, r i = ∑ i : Fin n, ∑ j : Fin n, P i j * q j := by rfl
      _ = ∑ j : Fin n, ∑ i : Fin n, P i j * q j := by rw [Finset.sum_comm]
      _ = ∑ j : Fin n, (∑ i : Fin n, P i j) * q j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul]
      _ = ∑ j : Fin n, q j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hcol j, one_mul]
      _ = 1 := hq_sum
  have hr_pos_of_hp_pos : ∀ i, 0 < p i → 0 < r i := by
    intro i hp_pos
    have hrow_ne : (∑ j : Fin n, P i j) ≠ 0 := by rw [hrow i]; norm_num
    obtain ⟨j, _hjmem, hPne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hrow_ne
    have hPpos : 0 < P i j := lt_of_le_of_ne (hP_nonneg i j) (Ne.symm hPne)
    have hqpos : 0 < q j := by
      by_contra hqnot
      have hq0 : q j = 0 := le_antisymm (le_of_not_gt hqnot) (hq_nonneg j)
      have hpP0 := hsupport_zero i j hq0
      have hP0 : P i j = 0 := (mul_eq_zero.mp hpP0).resolve_left hp_pos.ne'
      exact hPne hP0
    have htermpos : 0 < P i j * q j := mul_pos hPpos hqpos
    have hle : P i j * q j ≤ ∑ k : Fin n, P i k * q k := by
      exact Finset.single_le_sum (fun k _ => mul_nonneg (hP_nonneg i k) (hq_nonneg k))
        (Finset.mem_univ j)
    dsimp [r]
    exact lt_of_lt_of_le htermpos hle
  have hrow_log_le : ∀ i, 0 < p i →
      (∑ j : Fin n, P i j * Real.log (q j)) ≤ Real.log (r i) := by
    intro i hp_pos
    have hzero : ∀ j, q j = 0 → P i j = 0 := by
      intro j hq0
      have hpP0 := hsupport_zero i j hq0
      exact (mul_eq_zero.mp hpP0).resolve_left hp_pos.ne'
    simpa [r] using weighted_log_le_log_weighted_of_zero_weight (fun j => P i j) q
      (fun j => hP_nonneg i j) (hrow i) hq_nonneg hzero
  have hcross_le :
      (∑ i : Fin n, ∑ j : Fin n, p i * P i j * Real.log (q j)) ≤
        ∑ i : Fin n, p i * Real.log (r i) := by
    refine Finset.sum_le_sum ?_
    intro i _
    by_cases hp0 : p i = 0
    · simp [hp0]
    · have hp_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hp0)
      have hle := hrow_log_le i hp_pos
      have hmul := mul_le_mul_of_nonneg_left hle hp_pos.le
      calc
        (∑ j : Fin n, p i * P i j * Real.log (q j))
            = p i * (∑ j : Fin n, P i j * Real.log (q j)) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun j _ => ?_
                ring
        _ ≤ p i * Real.log (r i) := hmul
  have hgibbs : 0 ≤ (∑ i : Fin n, p i * Real.log (p i)) -
      (∑ i : Fin n, p i * Real.log (r i)) :=
    finite_gibbs_nonneg p r hp_nonneg hr_nonneg hp_sum hr_sum hr_pos_of_hp_pos
  have hrel : relative_entropy_real ρ σ =
      (∑ i : Fin n, p i * Real.log (p i)) -
        (∑ i : Fin n, ∑ j : Fin n, p i * P i j * Real.log (q j)) := by
    unfold relative_entropy_real
    calc
      (Matrix.trace (ρ.matrix * (matrix_log ρ.matrix - matrix_log σ.matrix))).re
          = (Matrix.trace (ρ.matrix * matrix_log ρ.matrix)).re -
              (Matrix.trace (ρ.matrix * matrix_log σ.matrix)).re := by
              simp [Matrix.mul_sub, Matrix.trace_sub]
      _ = (∑ i : Fin n, p i * Real.log (p i)) -
            (∑ i : Fin n, ∑ j : Fin n, p i * P i j * Real.log (q j)) := by
              rw [trace_self_log_eq_sum ρ, trace_cross_log_eq_sum ρ σ]
  have hlower : (∑ i : Fin n, p i * Real.log (p i)) -
      (∑ i : Fin n, p i * Real.log (r i)) ≤ relative_entropy_real ρ σ := by
    rw [hrel]
    linarith
  exact hgibbs.trans hlower

/-- Among diagonal reference states with the same support condition, `Δρ` minimises
`D(ρ ‖ -)`. -/
theorem relative_entropy_pinching_le_of_diagonal {n : ℕ} (ρ τ : DensityMatrix n)
    (hτdiag : ∀ i j, i ≠ j → τ.matrix i j = 0)
    (h : support_le ρ τ) :
    relative_entropy_real ρ (pinching ρ) ≤ relative_entropy_real ρ τ := by
  have hpyth := relative_entropy_pinching_add_of_diagonal ρ τ hτdiag
  have hsupport : support_le (pinching ρ) τ :=
    support_le_pinching_of_diagonal ρ τ hτdiag h
  have hnonneg : 0 ≤ relative_entropy_real (pinching ρ) τ :=
    relative_entropy_real_nonneg_of_support (pinching ρ) τ hsupport
  rw [hpyth]
  linarith

theorem pinching_entropy_inequality {n : ℕ} (ρ : DensityMatrix n) :
    von_neumann_entropy ρ ≤ von_neumann_entropy (pinching ρ) := by
  have hD : 0 ≤ relative_entropy_real ρ (pinching ρ) :=
    relative_entropy_real_nonneg_of_support ρ (pinching ρ) (support_le_pinching ρ)
  rw [relative_entropy_pinching_eq_entropy_diff ρ] at hD
  linarith

/-- Entropy depends only on the matrix, not on the particular `DensityMatrix` proof bundle
    (same technique as `pinching_entropy_inequality`: match characteristic-polynomial roots). -/
private lemma von_neumann_entropy_eq_of_matrix_eq {n : ℕ} {ρ τ : DensityMatrix n}
    (h : ρ.matrix = τ.matrix) : von_neumann_entropy ρ = von_neumann_entropy τ := by
  classical
  have hcp : ρ.matrix.charpoly = τ.matrix.charpoly := by rw [h]
  have hroots_ρ : ρ.matrix.charpoly.roots
      = Multiset.map ((RCLike.ofReal : ℝ → ℂ) ∘ ρ.toIsHermitian.eigenvalues) Finset.univ.val :=
    ρ.toIsHermitian.roots_charpoly_eq_eigenvalues
  have hroots_τ : τ.matrix.charpoly.roots
      = Multiset.map ((RCLike.ofReal : ℝ → ℂ) ∘ τ.toIsHermitian.eigenvalues) Finset.univ.val :=
    τ.toIsHermitian.roots_charpoly_eq_eigenvalues
  have hmap_eq :
      Multiset.map ((RCLike.ofReal : ℝ → ℂ) ∘ ρ.toIsHermitian.eigenvalues) Finset.univ.val
        = Multiset.map ((RCLike.ofReal : ℝ → ℂ) ∘ τ.toIsHermitian.eigenvalues) Finset.univ.val := by
    rw [← hroots_ρ, ← hroots_τ, hcp]
  have hofReal_inj : Function.Injective (RCLike.ofReal : ℝ → ℂ) := RCLike.ofReal_injective
  have hmset_eq :
      Multiset.map ρ.toIsHermitian.eigenvalues Finset.univ.val
        = Multiset.map τ.toIsHermitian.eigenvalues Finset.univ.val := by
    have hcomp := hmap_eq
    rw [← Multiset.map_map, ← Multiset.map_map] at hcomp
    exact Multiset.map_injective hofReal_inj hcomp
  have hmset_eq' :
      Multiset.map ρ.eigenvalues Finset.univ.val
        = Multiset.map τ.eigenvalues Finset.univ.val := by
    simpa [DensityMatrix.eigenvalues_eq] using hmset_eq
  have hsum :
      (∑ i : Fin n, Real.negMulLog (ρ.eigenvalues i))
        = ∑ i : Fin n, Real.negMulLog (τ.eigenvalues i) := by
    have e1 : (∑ i : Fin n, Real.negMulLog (ρ.eigenvalues i))
        = (Multiset.map Real.negMulLog (Multiset.map ρ.eigenvalues Finset.univ.val)).sum := by
      rw [Multiset.map_map]; rfl
    have e2 : (∑ i : Fin n, Real.negMulLog (τ.eigenvalues i))
        = (Multiset.map Real.negMulLog (Multiset.map τ.eigenvalues Finset.univ.val)).sum := by
      rw [Multiset.map_map]; rfl
    rw [e1, e2, hmset_eq']
  have hentropy_ρ :
      (∑ i : Fin n, Real.negMulLog (ρ.eigenvalues i)) = von_neumann_entropy ρ := by
    unfold von_neumann_entropy
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _hi => ?_
    by_cases hzero : ρ.eigenvalues i = 0
    · simp [hzero, Real.negMulLog_zero]
    · simp [hzero, Real.negMulLog_eq_neg]
  have hentropy_τ :
      (∑ i : Fin n, Real.negMulLog (τ.eigenvalues i)) = von_neumann_entropy τ := by
    unfold von_neumann_entropy
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _hi => ?_
    by_cases hzero : τ.eigenvalues i = 0
    · simp [hzero, Real.negMulLog_zero]
    · simp [hzero, Real.negMulLog_eq_neg]
  rw [← hentropy_ρ, ← hentropy_τ, hsum]

/-- If `v` is in the kernel of the mixture `pρ+(1-p)σ` (with `0<p<1`), it is in the kernel of both
    `ρ` and `σ`: the quadratic forms `⟨v,ρv⟩,⟨v,σv⟩ ≥ 0` sum (weighted by `p,1-p>0`) to `0`, so both
    vanish, and `PosSemidef.dotProduct_mulVec_zero_iff` upgrades that to `ρv=0`, `σv=0`. -/
private lemma mixture_ker_sub {n : ℕ} (ρ σ : DensityMatrix n) (p : ℝ) (h_p : 0 ≤ p ∧ p ≤ 1)
    (hp_pos : 0 < p) (hq_pos : 0 < 1 - p) (v : Fin n → ℂ)
    (hv : (density_matrix_mixture ρ σ p h_p).matrix *ᵥ v = 0) :
    ρ.matrix *ᵥ v = 0 ∧ σ.matrix *ᵥ v = 0 := by
  have hρpsd : Matrix.PosSemidef ρ.matrix := ρ.positive
  have hσpsd : Matrix.PosSemidef σ.matrix := σ.positive
  set a : ℂ := star v ⬝ᵥ (ρ.matrix *ᵥ v) with ha_def
  set b : ℂ := star v ⬝ᵥ (σ.matrix *ᵥ v) with hb_def
  have ha_le : (0 : ℂ) ≤ a := by
    rw [ha_def]
    exact hρpsd.dotProduct_mulVec_nonneg v
  have hb_le : (0 : ℂ) ≤ b := by
    rw [hb_def]
    exact hσpsd.dotProduct_mulVec_nonneg v
  rw [Complex.le_def] at ha_le hb_le
  simp only [Complex.zero_re, Complex.zero_im] at ha_le hb_le
  have hmix : (density_matrix_mixture ρ σ p h_p).matrix =
      (p : ℂ) • ρ.matrix + ((1 - p : ℝ) : ℂ) • σ.matrix := rfl
  have hdot0 : star v ⬝ᵥ ((density_matrix_mixture ρ σ p h_p).matrix *ᵥ v) = 0 := by
    rw [hv]; simp
  rw [hmix, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_smul, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, ← ha_def, ← hb_def] at hdot0
  have hre : p * a.re + (1 - p) * b.re = 0 := by
    have hre0 := congrArg Complex.re hdot0
    simpa [Complex.add_re, Complex.mul_re] using hre0
  have ha_re_zero : a.re = 0 := by nlinarith [ha_le.1, hb_le.1]
  have hb_re_zero : b.re = 0 := by nlinarith [ha_le.1, hb_le.1]
  have ha_zero : a = 0 := Complex.ext ha_re_zero ha_le.2.symm
  have hb_zero : b = 0 := Complex.ext hb_re_zero hb_le.2.symm
  exact ⟨(hρpsd.dotProduct_mulVec_zero_iff v).mp ha_zero,
    (hσpsd.dotProduct_mulVec_zero_iff v).mp hb_zero⟩

private lemma support_le_mixture_left {n : ℕ} (ρ σ : DensityMatrix n) (p : ℝ)
    (h_p : 0 ≤ p ∧ p ≤ 1) (hp_pos : 0 < p) (hq_pos : 0 < 1 - p) :
    support_le ρ (density_matrix_mixture ρ σ p h_p) := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  exact (mixture_ker_sub ρ σ p h_p hp_pos hq_pos v hv).1

private lemma support_le_mixture_right {n : ℕ} (ρ σ : DensityMatrix n) (p : ℝ)
    (h_p : 0 ≤ p ∧ p ≤ 1) (hp_pos : 0 < p) (hq_pos : 0 < 1 - p) :
    support_le σ (density_matrix_mixture ρ σ p h_p) := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  exact (mixture_ker_sub ρ σ p h_p hp_pos hq_pos v hv).2

/-- Standard "Klein's inequality implies concavity" argument: with `τ := pρ+(1-p)σ`,
    `p·D(ρ‖τ) + (1-p)·D(σ‖τ) = S(τ) - p·S(ρ) - (1-p)·S(σ)` by trace linearity, and the LHS is
    `≥ 0` by Klein (`relative_entropy_real_nonneg_of_support`). Boundary cases `p=0,1` are direct
    (the mixture collapses onto `σ` resp. `ρ`). -/
theorem entropy_concave {n : ℕ} (ρ σ : DensityMatrix n) (p : ℝ)
    (h_p : 0 ≤ p ∧ p ≤ 1) :
    von_neumann_entropy (density_matrix_mixture ρ σ p h_p) ≥
      p * von_neumann_entropy ρ + (1 - p) * von_neumann_entropy σ := by
  rcases eq_or_lt_of_le h_p.1 with hp0 | hp_pos
  · have hmatrix : (density_matrix_mixture ρ σ p h_p).matrix = σ.matrix := by
      simp [density_matrix_mixture, ← hp0]
    have hentropy := von_neumann_entropy_eq_of_matrix_eq hmatrix
    rw [hentropy, ← hp0]
    simp
  · rcases eq_or_lt_of_le h_p.2 with hp1 | hp_lt1
    · have hmatrix : (density_matrix_mixture ρ σ p h_p).matrix = ρ.matrix := by
        simp [density_matrix_mixture, hp1]
      have hentropy := von_neumann_entropy_eq_of_matrix_eq hmatrix
      rw [hentropy, hp1]
      simp
    · have hq_pos : 0 < 1 - p := by linarith
      set τ := density_matrix_mixture ρ σ p h_p with hτ_def
      have hsupp_ρ : support_le ρ τ := support_le_mixture_left ρ σ p h_p hp_pos hq_pos
      have hsupp_σ : support_le σ τ := support_le_mixture_right ρ σ p h_p hp_pos hq_pos
      have hDρ : 0 ≤ relative_entropy_real ρ τ := relative_entropy_real_nonneg_of_support ρ τ hsupp_ρ
      have hDσ : 0 ≤ relative_entropy_real σ τ := relative_entropy_real_nonneg_of_support σ τ hsupp_σ
      have hτ_mat : τ.matrix = (p : ℂ) • ρ.matrix + ((1 - p : ℝ) : ℂ) • σ.matrix := rfl
      have hcross : (p : ℂ) * Matrix.trace (ρ.matrix * matrix_log τ.matrix) +
          ((1 - p : ℝ) : ℂ) * Matrix.trace (σ.matrix * matrix_log τ.matrix) =
          Matrix.trace (τ.matrix * matrix_log τ.matrix) := by
        generalize matrix_log τ.matrix = X
        rw [hτ_mat, Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.smul_mul,
          Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
      have hcross_re : p * (Matrix.trace (ρ.matrix * matrix_log τ.matrix)).re +
          (1 - p) * (Matrix.trace (σ.matrix * matrix_log τ.matrix)).re =
          (Matrix.trace (τ.matrix * matrix_log τ.matrix)).re := by
        have := congrArg Complex.re hcross
        simpa [Complex.add_re, Complex.mul_re] using this
      have hDρ_eq : relative_entropy_real ρ τ =
          (Matrix.trace (ρ.matrix * matrix_log ρ.matrix)).re -
            (Matrix.trace (ρ.matrix * matrix_log τ.matrix)).re := by
        unfold relative_entropy_real
        simp [Matrix.mul_sub, Matrix.trace_sub]
      have hDσ_eq : relative_entropy_real σ τ =
          (Matrix.trace (σ.matrix * matrix_log σ.matrix)).re -
            (Matrix.trace (σ.matrix * matrix_log τ.matrix)).re := by
        unfold relative_entropy_real
        simp [Matrix.mul_sub, Matrix.trace_sub]
      have hSρ : (Matrix.trace (ρ.matrix * matrix_log ρ.matrix)).re = - von_neumann_entropy ρ := by
        rw [trace_self_log_eq_sum ρ]
        unfold von_neumann_entropy
        rw [neg_neg]
        refine Finset.sum_congr rfl fun i _hi => ?_
        by_cases hzero : ρ.eigenvalues i = 0
        · simp [hzero]
        · simp [hzero]
      have hSσ : (Matrix.trace (σ.matrix * matrix_log σ.matrix)).re = - von_neumann_entropy σ := by
        rw [trace_self_log_eq_sum σ]
        unfold von_neumann_entropy
        rw [neg_neg]
        refine Finset.sum_congr rfl fun i _hi => ?_
        by_cases hzero : σ.eigenvalues i = 0
        · simp [hzero]
        · simp [hzero]
      have hSτ : (Matrix.trace (τ.matrix * matrix_log τ.matrix)).re = - von_neumann_entropy τ := by
        rw [trace_self_log_eq_sum τ]
        unfold von_neumann_entropy
        rw [neg_neg]
        refine Finset.sum_congr rfl fun i _hi => ?_
        by_cases hzero : τ.eigenvalues i = 0
        · simp [hzero]
        · simp [hzero]
      have hcombine : 0 ≤ p * relative_entropy_real ρ τ + (1 - p) * relative_entropy_real σ τ :=
        add_nonneg (mul_nonneg hp_pos.le hDρ) (mul_nonneg hq_pos.le hDσ)
      rw [hDρ_eq, hDσ_eq, hSρ, hSσ] at hcombine
      have hexpand :
          p * (- von_neumann_entropy ρ - (Matrix.trace (ρ.matrix * matrix_log τ.matrix)).re) +
            (1 - p) * (- von_neumann_entropy σ - (Matrix.trace (σ.matrix * matrix_log τ.matrix)).re)
          = - p * von_neumann_entropy ρ - (1 - p) * von_neumann_entropy σ -
              (p * (Matrix.trace (ρ.matrix * matrix_log τ.matrix)).re +
                (1 - p) * (Matrix.trace (σ.matrix * matrix_log τ.matrix)).re) := by ring
      rw [hexpand, hcross_re, hSτ] at hcombine
      linarith

/-- Klein's inequality — now a THEOREM (was a FALSE unconditional axiom). Unconditional over EReal:
    on support it reduces to the scoped finite fact; off support the value is `⊤ ≥ 0`. -/
theorem relative_entropy_nonneg {n : ℕ} (ρ σ : DensityMatrix n) :
    (0 : EReal) ≤ relative_entropy ρ σ := by
  classical
  by_cases h : support_le ρ σ
  · rw [relative_entropy_of_support h]
    exact_mod_cast relative_entropy_real_nonneg_of_support ρ σ h
  · rw [relative_entropy_eq_top h]
    exact le_top

/-- Equality case of Klein's inequality: on full support, `D(ρ‖σ)=0` forces `ρ=σ`. Reruns the
    Klein setup (`U,V,W,P,p,q,r`), extracts the two Jensen tightnesses (the Gibbs step via
    `finite_gibbs_eq_zero`, the per-row step via `weighted_log_eq_weighted_of_zero_weight`) to get
    `∀ i j, W i j ≠ 0 → q j = p i`, then an entrywise computation `W·diag q·W⁻¹ = diag p` (using
    `W·star W = 1`) reconstructs `ρ.matrix = σ.matrix` via the shared spectral decomposition. -/
theorem relative_entropy_eq_zero_iff {n : ℕ} (ρ σ : DensityMatrix n) (h : support_le ρ σ) :
    relative_entropy_real ρ σ = 0 ↔ ρ = σ := by
  constructor
  · intro heq0
    classical
    let U := ρ.toIsHermitian.eigenvectorUnitary
    let V := σ.toIsHermitian.eigenvectorUnitary
    let W : Matrix (Fin n) (Fin n) ℂ :=
      star (U : Matrix (Fin n) (Fin n) ℂ) * (V : Matrix (Fin n) (Fin n) ℂ)
    let P : Fin n → Fin n → ℝ := fun i j => Complex.normSq (W i j)
    let p : Fin n → ℝ := ρ.eigenvalues
    let q : Fin n → ℝ := σ.eigenvalues
    let r : Fin n → ℝ := fun i => ∑ j : Fin n, P i j * q j
    have hp_nonneg : ∀ i, 0 ≤ p i := by intro i; exact eigenvalue_nonneg ρ i
    have hq_nonneg : ∀ j, 0 ≤ q j := by intro j; exact eigenvalue_nonneg σ j
    have hp_sum : ∑ i : Fin n, p i = 1 := by
      simpa [p] using density_eigenvalues_sum_eq_one ρ
    have hq_sum : ∑ j : Fin n, q j = 1 := by
      simpa [q] using density_eigenvalues_sum_eq_one σ
    have hP_nonneg : ∀ i j, 0 ≤ P i j := by intro i j; exact Complex.normSq_nonneg _
    have hrow : ∀ i, ∑ j : Fin n, P i j = 1 := by
      intro i; simpa [P, W, U, V] using overlap_row_sum U V i
    have hcol : ∀ j, ∑ i : Fin n, P i j = 1 := by
      intro j; simpa [P, W, U, V] using overlap_col_sum U V j
    have hsupport_zero : ∀ i j, q j = 0 → p i * P i j = 0 := by
      intro i j hq0
      have hc := support_zero_eigen_overlap_mul_eq_zero ρ σ h i j (by simpa [q] using hq0)
      simpa [p, P, W, U, V] using real_mul_normSq_eq_zero_of_ofReal_mul_eq_zero hc
    have hr_nonneg : ∀ i, 0 ≤ r i := by
      intro i; dsimp [r]
      exact Finset.sum_nonneg (by intro j _; exact mul_nonneg (hP_nonneg i j) (hq_nonneg j))
    have hr_sum : ∑ i : Fin n, r i = 1 := by
      calc
        ∑ i : Fin n, r i = ∑ i : Fin n, ∑ j : Fin n, P i j * q j := by rfl
        _ = ∑ j : Fin n, ∑ i : Fin n, P i j * q j := by rw [Finset.sum_comm]
        _ = ∑ j : Fin n, (∑ i : Fin n, P i j) * q j := by
              refine Finset.sum_congr rfl fun j _ => ?_; rw [Finset.sum_mul]
        _ = ∑ j : Fin n, q j := by
              refine Finset.sum_congr rfl fun j _ => ?_; rw [hcol j, one_mul]
        _ = 1 := hq_sum
    have hr_pos_of_hp_pos : ∀ i, 0 < p i → 0 < r i := by
      intro i hp_pos
      have hrow_ne : (∑ j : Fin n, P i j) ≠ 0 := by rw [hrow i]; norm_num
      obtain ⟨j, _hjmem, hPne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hrow_ne
      have hPpos : 0 < P i j := lt_of_le_of_ne (hP_nonneg i j) (Ne.symm hPne)
      have hqpos : 0 < q j := by
        by_contra hqnot
        have hq0 : q j = 0 := le_antisymm (le_of_not_gt hqnot) (hq_nonneg j)
        have hpP0 := hsupport_zero i j hq0
        have hP0 : P i j = 0 := (mul_eq_zero.mp hpP0).resolve_left hp_pos.ne'
        exact hPne hP0
      have htermpos : 0 < P i j * q j := mul_pos hPpos hqpos
      have hle : P i j * q j ≤ ∑ k : Fin n, P i k * q k :=
        Finset.single_le_sum (fun k _ => mul_nonneg (hP_nonneg i k) (hq_nonneg k))
          (Finset.mem_univ j)
      dsimp [r]; exact lt_of_lt_of_le htermpos hle
    have hrow_log_le : ∀ i, 0 < p i →
        (∑ j : Fin n, P i j * Real.log (q j)) ≤ Real.log (r i) := by
      intro i hp_pos
      have hzero : ∀ j, q j = 0 → P i j = 0 := by
        intro j hq0
        have hpP0 := hsupport_zero i j hq0
        exact (mul_eq_zero.mp hpP0).resolve_left hp_pos.ne'
      simpa [r] using weighted_log_le_log_weighted_of_zero_weight (fun j => P i j) q
        (fun j => hP_nonneg i j) (hrow i) hq_nonneg hzero
    have hcross_le :
        (∑ i : Fin n, ∑ j : Fin n, p i * P i j * Real.log (q j)) ≤
          ∑ i : Fin n, p i * Real.log (r i) := by
      refine Finset.sum_le_sum ?_
      intro i _
      by_cases hp0 : p i = 0
      · simp [hp0]
      · have hp_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hp0)
        have hle := hrow_log_le i hp_pos
        have hmul := mul_le_mul_of_nonneg_left hle hp_pos.le
        calc
          (∑ j : Fin n, p i * P i j * Real.log (q j))
              = p i * (∑ j : Fin n, P i j * Real.log (q j)) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  ring
          _ ≤ p i * Real.log (r i) := hmul
    have hgibbs : 0 ≤ (∑ i : Fin n, p i * Real.log (p i)) -
        (∑ i : Fin n, p i * Real.log (r i)) :=
      finite_gibbs_nonneg p r hp_nonneg hr_nonneg hp_sum hr_sum hr_pos_of_hp_pos
    have hrel : relative_entropy_real ρ σ =
        (∑ i : Fin n, p i * Real.log (p i)) -
          (∑ i : Fin n, ∑ j : Fin n, p i * P i j * Real.log (q j)) := by
      unfold relative_entropy_real
      calc
        (Matrix.trace (ρ.matrix * (matrix_log ρ.matrix - matrix_log σ.matrix))).re
            = (Matrix.trace (ρ.matrix * matrix_log ρ.matrix)).re -
                (Matrix.trace (ρ.matrix * matrix_log σ.matrix)).re := by
                simp [Matrix.mul_sub, Matrix.trace_sub]
        _ = (∑ i : Fin n, p i * Real.log (p i)) -
              (∑ i : Fin n, ∑ j : Fin n, p i * P i j * Real.log (q j)) := by
                rw [trace_self_log_eq_sum ρ, trace_cross_log_eq_sum ρ σ]
    have hlower : (∑ i : Fin n, p i * Real.log (p i)) -
        (∑ i : Fin n, p i * Real.log (r i)) ≤ relative_entropy_real ρ σ := by
      rw [hrel]; linarith
    -- Squeeze both Jensen steps to equality using `heq0 : relative_entropy_real ρ σ = 0`.
    have hA_le : (∑ i : Fin n, p i * Real.log (p i)) -
        (∑ i : Fin n, p i * Real.log (r i)) ≤ 0 := heq0 ▸ hlower
    have hA0 : (∑ i : Fin n, p i * Real.log (p i)) -
        (∑ i : Fin n, p i * Real.log (r i)) = 0 := le_antisymm hA_le hgibbs
    have hr_eq_p : ∀ i, r i = p i :=
      finite_gibbs_eq_zero p r hp_nonneg hr_nonneg hp_sum hr_sum hr_pos_of_hp_pos hA0
    have hB0 : (∑ i : Fin n, p i * Real.log (r i)) -
        (∑ i : Fin n, ∑ j : Fin n, p i * P i j * Real.log (q j)) = 0 := by
      rw [hrel] at heq0; linarith [hA0, heq0]
    have hcross_term_nonneg : ∀ i : Fin n,
        0 ≤ p i * Real.log (r i) - ∑ j : Fin n, p i * P i j * Real.log (q j) := by
      intro i
      by_cases hp0 : p i = 0
      · simp [hp0]
      · have hp_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hp0)
        have hle := hrow_log_le i hp_pos
        have heqsum : (∑ j : Fin n, p i * P i j * Real.log (q j))
            = p i * (∑ j : Fin n, P i j * Real.log (q j)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [heqsum]
        have hmul := mul_le_mul_of_nonneg_left hle hp_pos.le
        linarith [hmul]
    have hcross_sum_zero :
        ∑ i : Fin n, (p i * Real.log (r i) - ∑ j : Fin n, p i * P i j * Real.log (q j)) = 0 := by
      rw [Finset.sum_sub_distrib]; linarith [hB0]
    have hcross_term_zero : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        p i * Real.log (r i) - ∑ j : Fin n, p i * P i j * Real.log (q j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hcross_term_nonneg i)).mp hcross_sum_zero
    have hrow_log_eq : ∀ i, 0 < p i →
        (∑ j : Fin n, P i j * Real.log (q j)) = Real.log (r i) := by
      intro i hp_pos
      have hzero := hcross_term_zero i (Finset.mem_univ i)
      have heqsum : (∑ j : Fin n, p i * P i j * Real.log (q j))
          = p i * (∑ j : Fin n, P i j * Real.log (q j)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [heqsum] at hzero
      have : p i * (∑ j : Fin n, P i j * Real.log (q j)) = p i * Real.log (r i) := by linarith
      exact mul_left_cancel₀ hp_pos.ne' this
    -- The global overlap fact: `P i j ≠ 0 → q j = p i`, valid for EVERY `i` (including `p i = 0`).
    have hoverlap : ∀ i j, P i j ≠ 0 → q j = p i := by
      intro i j hPne
      by_cases hp0 : p i = 0
      · have hri0 : r i = 0 := (hr_eq_p i).trans hp0
        have hterm_nonneg : ∀ k ∈ (Finset.univ : Finset (Fin n)), 0 ≤ P i k * q k :=
          fun k _ => mul_nonneg (hP_nonneg i k) (hq_nonneg k)
        have hterm_sum_zero : ∑ k : Fin n, P i k * q k = 0 := hri0
        have hterm_zero := (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hterm_sum_zero
        have hj0 := hterm_zero j (Finset.mem_univ j)
        have : q j = 0 := (mul_eq_zero.mp hj0).resolve_left hPne
        rw [this, hp0]
      · have hp_pos : 0 < p i := lt_of_le_of_ne (hp_nonneg i) (Ne.symm hp0)
        have hzero : ∀ k, q k = 0 → P i k = 0 := by
          intro k hq0
          have hpP0 := hsupport_zero i k hq0
          exact (mul_eq_zero.mp hpP0).resolve_left hp_pos.ne'
        have := weighted_log_eq_weighted_of_zero_weight (fun k => P i k) q
          (fun k => hP_nonneg i k) (hrow i) hq_nonneg hzero (hrow_log_eq i hp_pos) j hPne
        rw [this]; exact hr_eq_p i
    -- Entrywise reconstruction: `W · diag q · star W = diag p`, using `hoverlap` and unitarity.
    have hWstarW : W * star W = 1 := overlap_mul_star U V
    have hWEW : W * Matrix.diagonal (fun j : Fin n => (q j : ℂ)) * star W =
        Matrix.diagonal (fun i : Fin n => (p i : ℂ)) := by
      ext k l
      have hlhs : (W * Matrix.diagonal (fun j : Fin n => (q j : ℂ)) * star W) k l
          = ∑ j : Fin n, W k j * (q j : ℂ) * star (W l j) := by
        simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, mul_assoc]
      have hswap : ∀ j : Fin n, W k j * (q j : ℂ) * star (W l j)
          = W k j * (p k : ℂ) * star (W l j) := by
        intro j
        by_cases hWkj : W k j = 0
        · simp [hWkj]
        · have hPne : P k j ≠ 0 := by
            dsimp [P]; exact fun hc => hWkj (Complex.normSq_eq_zero.mp hc)
          rw [hoverlap k j hPne]
      have hsum_eq : (∑ j : Fin n, W k j * (q j : ℂ) * star (W l j))
          = (p k : ℂ) * (W * star W) k l := by
        rw [Finset.sum_congr rfl (fun j _ => hswap j)]
        rw [Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.star_apply]
        ring
      rw [hlhs, hsum_eq, hWstarW]
      simp [Matrix.diagonal_apply, Matrix.one_apply]
    have hUW : (U : Matrix (Fin n) (Fin n) ℂ) * W = (V : Matrix (Fin n) (Fin n) ℂ) := by
      have hUU : (U : Matrix (Fin n) (Fin n) ℂ) * star (U : Matrix (Fin n) (Fin n) ℂ) = 1 :=
        (Matrix.mem_unitaryGroup_iff).mp U.2
      dsimp [W]
      rw [← Matrix.mul_assoc, hUU, one_mul]
    have hmat : ρ.matrix = σ.matrix := by
      have hρ : ρ.matrix =
          (U : Matrix (Fin n) (Fin n) ℂ) *
            Matrix.diagonal (fun i : Fin n => (p i : ℂ)) *
            star (U : Matrix (Fin n) (Fin n) ℂ) := by
        simpa [U, p] using density_spectral ρ
      have hσ : σ.matrix =
          (V : Matrix (Fin n) (Fin n) ℂ) *
            Matrix.diagonal (fun j : Fin n => (q j : ℂ)) *
            star (V : Matrix (Fin n) (Fin n) ℂ) := by
        simpa [V, q] using density_spectral σ
      rw [hρ, ← hWEW, hσ, ← hUW]
      simp only [Matrix.mul_assoc, StarMul.star_mul]
    have hDM : ρ = σ := by
      cases ρ; cases σ; simp_all
    exact hDM
  · rintro rfl
    simp [relative_entropy_real]

/-! ## Refutation: UNCONDITIONAL joint convexity of the finite value is FALSE

`relative_entropy_real` carries the junk convention `Real.log 0 = 0` off the support of `σ`.
Without `support_le` hypotheses on BOTH pairs, joint convexity fails. Take
`ρ₁ = ρ₂ = σ₁ = |0⟩⟨0|`, `σ₂ = |1⟩⟨1|`, `p = 1/2`: the σ-mixture `I/2` has full support, so the
LHS is the honest value `log 2 > 0`, while `relative_entropy_real |0⟩⟨0| |1⟩⟨1| = 0` is junk (the
true relative entropy is `+∞`), so the RHS is `0`. Same failure mode as the removed FALSE
unconditional `relative_entropy_nonneg` axiom. -/

/-- The mixture's matrix, definitionally. -/
private lemma mixture_matrix_eq {n : ℕ} (ρ σ : DensityMatrix n) (p : ℝ) (h_p : 0 ≤ p ∧ p ≤ 1) :
    (density_matrix_mixture ρ σ p h_p).matrix
      = (p : ℂ) • ρ.matrix + ((1 - p : ℝ) : ℂ) • σ.matrix := rfl

/-- Sandwiching `A = U D U*` by the unitary recovers `D`. Stated for an arbitrary unitary so the
    rewrite never has to abstract `ρ.matrix` under `eigenvectorUnitary` (dependent-motive trap). -/
private lemma unitary_sandwich {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A D : Matrix (Fin n) (Fin n) ℂ)
    (h : A = (U : Matrix (Fin n) (Fin n) ℂ) * D * star (U : Matrix (Fin n) (Fin n) ℂ)) :
    star (U : Matrix (Fin n) (Fin n) ℂ) * A * (U : Matrix (Fin n) (Fin n) ℂ) = D := by
  subst h
  simp only [Matrix.mul_assoc]
  rw [Unitary.coe_star_mul_self, Matrix.mul_one, ← Matrix.mul_assoc,
    Unitary.coe_star_mul_self, Matrix.one_mul]

/-- Conjugating a density matrix by its own eigenvector unitary yields the eigenvalue diagonal. -/
private lemma density_diag_eq_conj {n : ℕ} (ρ : DensityMatrix n) :
    star (ρ.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * ρ.matrix *
        (ρ.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
      = Matrix.diagonal (fun i : Fin n => (ρ.eigenvalues i : ℂ)) :=
  unitary_sandwich _ _ _ (density_spectral ρ)

/-- Conjugation by a unitary is multiplicative on the sandwiched factors. -/
private lemma conj_mul_conj {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    (star (U : Matrix (Fin n) (Fin n) ℂ) * A * (U : Matrix (Fin n) (Fin n) ℂ)) *
        (star (U : Matrix (Fin n) (Fin n) ℂ) * B * (U : Matrix (Fin n) (Fin n) ℂ))
      = star (U : Matrix (Fin n) (Fin n) ℂ) * (A * B) * (U : Matrix (Fin n) (Fin n) ℂ) := by
  have h1 : (star (U : Matrix (Fin n) (Fin n) ℂ) * A * (U : Matrix (Fin n) (Fin n) ℂ)) *
      (star (U : Matrix (Fin n) (Fin n) ℂ) * B * (U : Matrix (Fin n) (Fin n) ℂ))
      = star (U : Matrix (Fin n) (Fin n) ℂ) * A *
          ((U : Matrix (Fin n) (Fin n) ℂ) * star (U : Matrix (Fin n) (Fin n) ℂ)) * B *
          (U : Matrix (Fin n) (Fin n) ℂ) := by
    simp only [Matrix.mul_assoc]
  have hUstar : (U : Matrix (Fin n) (Fin n) ℂ) * star (U : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    exact Unitary.coe_mul_star_self U
  rw [h1, hUstar, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

/-- Eigenvalues of an idempotent (projection) density matrix are `0` or `1`. -/
private lemma eigenvalues_of_idempotent {n : ℕ} (ρ : DensityMatrix n)
    (h : ρ.matrix * ρ.matrix = ρ.matrix) (i : Fin n) :
    ρ.eigenvalues i = 0 ∨ ρ.eigenvalues i = 1 := by
  have hD2 : Matrix.diagonal (fun j : Fin n => (ρ.eigenvalues j : ℂ)) *
      Matrix.diagonal (fun j : Fin n => (ρ.eigenvalues j : ℂ))
      = Matrix.diagonal (fun j : Fin n => (ρ.eigenvalues j : ℂ)) := by
    rw [← density_diag_eq_conj ρ, conj_mul_conj, h]
  rw [Matrix.diagonal_mul_diagonal] at hD2
  have hentry := congrFun (congrFun hD2 i) i
  simp only [Matrix.diagonal_apply_eq] at hentry
  have hreal : ρ.eigenvalues i * ρ.eigenvalues i = ρ.eigenvalues i := by
    exact_mod_cast hentry
  have hfactor : ρ.eigenvalues i * (ρ.eigenvalues i - 1) = 0 := by
    rw [mul_sub, mul_one, hreal, sub_self]
  rcases mul_eq_zero.mp hfactor with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith [sub_eq_zero.mp h1])

/-- `matrix_log` of an idempotent density matrix vanishes: every eigenvalue is `0` or `1`, and
    `Real.log 0 = Real.log 1 = 0` (the junk convention is doing real work here). -/
private lemma matrix_log_of_idempotent {n : ℕ} (ρ : DensityMatrix n)
    (h : ρ.matrix * ρ.matrix = ρ.matrix) :
    matrix_log ρ.matrix = 0 := by
  rw [density_log_diag ρ]
  have hz : (fun i : Fin n => (Real.log (ρ.eigenvalues i) : ℂ)) = fun _ => (0 : ℂ) := by
    funext i
    rcases eigenvalues_of_idempotent ρ h i with h0 | h1
    · rw [h0, Real.log_zero, Complex.ofReal_zero]
    · rw [h1, Real.log_one, Complex.ofReal_zero]
  rw [hz]
  simp

/-- Eigenvalues of a scalar density matrix `c • 1` are all `c`. -/
private lemma eigenvalues_of_smul_one {n : ℕ} (ρ : DensityMatrix n) (c : ℝ)
    (h : ρ.matrix = (c : ℂ) • 1) (i : Fin n) :
    ρ.eigenvalues i = c := by
  have hmid : ∀ (V : Matrix.unitaryGroup (Fin n) ℂ),
      star (V : Matrix (Fin n) (Fin n) ℂ) * ρ.matrix * (V : Matrix (Fin n) (Fin n) ℂ)
        = (c : ℂ) • 1 := by
    intro V
    rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Unitary.coe_star_mul_self]
  have hDc : Matrix.diagonal (fun j : Fin n => (ρ.eigenvalues j : ℂ))
      = (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← density_diag_eq_conj ρ, hmid]
  have hentry := congrFun (congrFun hDc i) i
  simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one] at hentry
  exact_mod_cast hentry

/-- `matrix_log` of a scalar density matrix `c • 1` is `(Real.log c) • 1`. -/
private lemma matrix_log_of_smul_one {n : ℕ} (ρ : DensityMatrix n) (c : ℝ)
    (h : ρ.matrix = (c : ℂ) • 1) :
    matrix_log ρ.matrix = ((Real.log c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [density_log_diag ρ]
  have hz : (fun i : Fin n => (Real.log (ρ.eigenvalues i) : ℂ))
      = fun _ : Fin n => ((Real.log c : ℝ) : ℂ) := by
    funext i
    rw [eigenvalues_of_smul_one ρ c h i]
  rw [hz]
  have hdiag : Matrix.diagonal (fun _ : Fin n => ((Real.log c : ℝ) : ℂ))
      = ((Real.log c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hUstar : (ρ.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      star (ρ.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    exact Unitary.coe_mul_star_self ρ.toIsHermitian.eigenvectorUnitary
  rw [hdiag, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUstar]

/-- `|0⟩⟨0|` on ℂ². -/
private noncomputable def ketZeroDM : DensityMatrix 2 :=
  { matrix := Matrix.diagonal ![1, 0]
    hermitian := by
      rw [Matrix.diagonal_conjTranspose]
      congr 1
      funext i
      fin_cases i <;> simp
    positive := by
      show Matrix.PosSemidef _
      refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
      fin_cases i <;> simp
    normalized := by
      rw [Matrix.trace_diagonal]
      simp [Fin.sum_univ_two] }

/-- `|1⟩⟨1|` on ℂ². -/
private noncomputable def ketOneDM : DensityMatrix 2 :=
  { matrix := Matrix.diagonal ![0, 1]
    hermitian := by
      rw [Matrix.diagonal_conjTranspose]
      congr 1
      funext i
      fin_cases i <;> simp
    positive := by
      show Matrix.PosSemidef _
      refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
      fin_cases i <;> simp
    normalized := by
      rw [Matrix.trace_diagonal]
      simp [Fin.sum_univ_two] }

private lemma ketZeroDM_idem : ketZeroDM.matrix * ketZeroDM.matrix = ketZeroDM.matrix := by
  show Matrix.diagonal ![1, 0] * Matrix.diagonal ![1, 0] = Matrix.diagonal ![1, 0]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

private lemma ketOneDM_idem : ketOneDM.matrix * ketOneDM.matrix = ketOneDM.matrix := by
  show Matrix.diagonal ![0, 1] * Matrix.diagonal ![0, 1] = Matrix.diagonal ![0, 1]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

private lemma half_mem : (0 : ℝ) ≤ 1/2 ∧ (1/2 : ℝ) ≤ 1 := by norm_num

/-- The ρ-mixture collapses back onto `|0⟩⟨0|`. -/
private lemma mix_rho_eq :
    (density_matrix_mixture ketZeroDM ketZeroDM (1/2) half_mem).matrix = ketZeroDM.matrix := by
  rw [mixture_matrix_eq]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The σ-mixture is the maximally mixed state `I/2` — full support. -/
private lemma mix_sigma_eq :
    (density_matrix_mixture ketZeroDM ketOneDM (1/2) half_mem).matrix
      = ((1/2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [mixture_matrix_eq]
  show ((1/2 : ℝ) : ℂ) • Matrix.diagonal ![1, 0] + ((1 - 1/2 : ℝ) : ℂ) • Matrix.diagonal ![0, 1]
      = ((1/2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;> (simp; try norm_num)

/-- LHS of the would-be joint convexity: the honest value `log 2`. -/
private lemma D_mix_eq_log_two :
    relative_entropy_real (density_matrix_mixture ketZeroDM ketZeroDM (1/2) half_mem)
      (density_matrix_mixture ketZeroDM ketOneDM (1/2) half_mem) = Real.log 2 := by
  unfold relative_entropy_real
  rw [mix_rho_eq, matrix_log_of_idempotent ketZeroDM ketZeroDM_idem,
    matrix_log_of_smul_one _ (1/2) mix_sigma_eq]
  rw [zero_sub, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_neg,
    Matrix.trace_smul, ketZeroDM.normalized]
  rw [smul_eq_mul, mul_one, Complex.neg_re, Complex.ofReal_re, one_div, Real.log_inv, neg_neg]

/-- First RHS term: `D_real(|0⟩⟨0| ‖ |0⟩⟨0|) = 0`. -/
private lemma D_ketZero_self : relative_entropy_real ketZeroDM ketZeroDM = 0 := by
  simp [relative_entropy_real]

/-- Second RHS term: junk-`0` (the true relative entropy is `+∞` — disjoint supports). -/
private lemma D_ketZero_ketOne : relative_entropy_real ketZeroDM ketOneDM = 0 := by
  unfold relative_entropy_real
  rw [matrix_log_of_idempotent ketZeroDM ketZeroDM_idem,
    matrix_log_of_idempotent ketOneDM ketOneDM_idem]
  simp

/-- REFUTATION (kernel-verified): joint convexity of the FINITE value `relative_entropy_real` is
    FALSE without `support_le` hypotheses on both pairs — instantiating at
    `ρ₁ = ρ₂ = σ₁ = |0⟩⟨0|`, `σ₂ = |1⟩⟨1|`, `p = 1/2` would force `log 2 ≤ 0`. Consequently the
    unconditional axiom `relative_entropy_jointly_convex` (below) makes the axiom set
    inconsistent; it must be rescoped with support hypotheses (the honest Lieb statement). -/
theorem not_relative_entropy_jointly_convex_unconditional :
    ¬ ∀ (n : ℕ) (ρ₁ ρ₂ σ₁ σ₂ : DensityMatrix n) (p : ℝ) (h_p : 0 ≤ p ∧ p ≤ 1),
      relative_entropy_real (density_matrix_mixture ρ₁ ρ₂ p h_p)
          (density_matrix_mixture σ₁ σ₂ p h_p)
        ≤ p * relative_entropy_real ρ₁ σ₁ + (1 - p) * relative_entropy_real ρ₂ σ₂ := by
  intro hall
  have h := hall 2 ketZeroDM ketZeroDM ketZeroDM ketOneDM (1/2) half_mem
  rw [D_mix_eq_log_two, D_ketZero_self, D_ketZero_ketOne] at h
  norm_num at h
  linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

#print axioms not_relative_entropy_jointly_convex_unconditional

/-- (finite-regime, scoped) Joint convexity (Lieb) — the one TRUE deep root; stays an axiom
    (Lieb's concavity theorem is absent from Mathlib). SCOPED to `support_le` on both pairs:
    the previous UNCONDITIONAL form was FALSE under the `Real.log 0 = 0` junk convention — see
    `not_relative_entropy_jointly_convex_unconditional` above for the kernel-verified
    counterexample (`ρ₁ = ρ₂ = σ₁ = |0⟩⟨0|`, `σ₂ = |1⟩⟨1|`, `p = 1/2` forces `log 2 ≤ 0`).
    On-support, both sides are the honest relative entropy and this is Lieb's theorem. -/
axiom relative_entropy_jointly_convex {n : ℕ}
    (ρ₁ ρ₂ σ₁ σ₂ : DensityMatrix n) (p : ℝ)
    (h_p : 0 ≤ p ∧ p ≤ 1)
    (h₁ : support_le ρ₁ σ₁) (h₂ : support_le ρ₂ σ₂) :
    relative_entropy_real
      (density_matrix_mixture ρ₁ ρ₂ p h_p)
      (density_matrix_mixture σ₁ σ₂ p h_p)
      ≤ p * relative_entropy_real ρ₁ σ₁ + (1 - p) * relative_entropy_real ρ₂ σ₂

theorem strong_subadditivity {nA nB nC : ℕ} (ρ_ABC : DensityMatrix (nA * nB * nC)) :
  let ρ_AB : DensityMatrix (nA * nB) := partial_trace_C ρ_ABC
  let ρ_BC : DensityMatrix (nB * nC) := partial_trace_first ρ_ABC
  let ρ_B : DensityMatrix nB := partial_trace_AC ρ_ABC
  von_neumann_entropy ρ_AB + von_neumann_entropy ρ_BC ≥
    von_neumann_entropy ρ_ABC + von_neumann_entropy ρ_B := by
  dsimp
  let σ := toMStateTriple ρ_ABC
  have h := Sᵥₙ_strong_subadditivity σ
  dsimp [σ] at h
  rw [toMStateTriple_traceLeft_traceRight] at h
  rw [toMStateTriple_assoc'_traceRight] at h
  rw [toMStateTriple_traceLeft] at h
  rw [← entropy_toMStateTriple] at h
  rw [← entropy_toMState] at h
  rw [← entropy_toMStatePair] at h
  rw [← entropy_toMStatePair] at h
  exact h

theorem araki_lieb_triangle {nA nB : ℕ} (ρ_AB : DensityMatrix (nA * nB)) :
    let ρ_A := partial_trace ρ_AB
    let ρ_B : DensityMatrix nB := partial_trace_A ρ_AB
    |von_neumann_entropy ρ_A - von_neumann_entropy ρ_B| ≤ von_neumann_entropy ρ_AB := by
  dsimp
  let σ := toMStatePair ρ_AB
  have h := Sᵥₙ_triangle_subaddivity σ
  dsimp [σ] at h
  rw [toMStatePair_traceRight] at h
  rw [toMStatePair_traceLeft] at h
  rw [← entropy_toMStatePair] at h
  rw [← entropy_toMState] at h
  rw [← entropy_toMState] at h
  exact h

noncomputable def conditional_entropy {nA nB : ℕ} (ρ_AB : DensityMatrix (nA * nB)) : ℝ :=
  let ρ_B : DensityMatrix nB := partial_trace_A ρ_AB
  von_neumann_entropy ρ_AB - von_neumann_entropy ρ_B

noncomputable def conditional_mutual_information {nA nB nC : ℕ}
    (ρ_ABC : DensityMatrix (nA * nB * nC)) : ℝ :=
  let ρ_AB : DensityMatrix (nA * nB) := partial_trace_C ρ_ABC
  let ρ_BC : DensityMatrix (nB * nC) := partial_trace_first ρ_ABC
  let ρ_B : DensityMatrix nB := partial_trace_AC ρ_ABC
  von_neumann_entropy ρ_AB + von_neumann_entropy ρ_BC -
    von_neumann_entropy ρ_ABC - von_neumann_entropy ρ_B

theorem conditional_mutual_information_nonneg {nA nB nC : ℕ}
    (ρ_ABC : DensityMatrix (nA * nB * nC)) :
    0 ≤ conditional_mutual_information ρ_ABC := by
  have h := strong_subadditivity ρ_ABC
  simp [conditional_mutual_information] at h ⊢
  linarith

/-! ## Soundness-audit infrastructure (2026-07-02)

Machine-checked closure properties showing that the support-scoped relative-entropy obligations
live ENTIRELY inside the honest (`support_le`) regime: their hypotheses imply `support_le` for the
states appearing on the LEFT side as well, so the junk `Real.log 0 = 0` convention cannot smuggle
a false finite value into either side. `relative_entropy_monotone` is now proved via physlib DPI;
`relative_entropy_jointly_convex` remains an axiom. -/

/-- `relative_entropy_real` depends only on the underlying matrices. -/
theorem relative_entropy_real_congr {n : ℕ} {ρ ρ' σ σ' : DensityMatrix n}
    (hρ : ρ.matrix = ρ'.matrix) (hσ : σ.matrix = σ'.matrix) :
    relative_entropy_real ρ σ = relative_entropy_real ρ' σ' := by
  unfold relative_entropy_real
  rw [hρ, hσ]

/-- If the two states have the same matrix, the relative entropy vanishes (log terms cancel). -/
theorem relative_entropy_real_eq_zero_of_matrix_eq {n : ℕ} {ρ σ : DensityMatrix n}
    (h : ρ.matrix = σ.matrix) : relative_entropy_real ρ σ = 0 := by
  unfold relative_entropy_real
  rw [h, sub_self, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]

/-- Pinching only reads the matrix. -/
theorem pinching_matrix_congr {n : ℕ} {ρ σ : DensityMatrix n} (h : ρ.matrix = σ.matrix) :
    (pinching ρ).matrix = (pinching σ).matrix := by
  show Matrix.diagonal _ = Matrix.diagonal _
  rw [h]

/-- Pinching is idempotent at the matrix level. -/
theorem pinching_pinching_matrix {n : ℕ} (ρ : DensityMatrix n) :
    (pinching (pinching ρ)).matrix = (pinching ρ).matrix := by
  show Matrix.diagonal (fun i => (pinching ρ).matrix i i)
      = Matrix.diagonal (fun i : Fin n => ρ.matrix i i)
  congr 1
  funext i
  show Matrix.diagonal (fun k : Fin n => ρ.matrix k k) i i = ρ.matrix i i
  simp

private lemma list_sum_posSemidef {n : ℕ} :
    ∀ l : List (Matrix (Fin n) (Fin n) ℂ),
      (∀ M ∈ l, Matrix.PosSemidef M) → Matrix.PosSemidef l.sum := by
  intro l
  induction l with
  | nil => intro _; simpa using (Matrix.PosSemidef.zero (n := Fin n) (R := ℂ))
  | cons A l ih =>
      intro hl
      rw [List.sum_cons]
      exact (hl A List.mem_cons_self).add
        (ih fun N hN => hl N (List.mem_cons_of_mem _ hN))

/-- If a sum of PSD matrices annihilates `v`, every summand annihilates `v`. -/
private lemma list_psd_sum_mulVec_zero {n : ℕ} (v : Fin n → ℂ) :
    ∀ l : List (Matrix (Fin n) (Fin n) ℂ),
      (∀ M ∈ l, Matrix.PosSemidef M) → l.sum *ᵥ v = 0 → ∀ M ∈ l, M *ᵥ v = 0 := by
  intro l
  induction l with
  | nil => intro _ _ M hM; exact (List.not_mem_nil hM).elim
  | cons A l ih =>
      intro hl hv
      have hA : Matrix.PosSemidef A := hl A List.mem_cons_self
      have hrest : ∀ M ∈ l, Matrix.PosSemidef M :=
        fun N hN => hl N (List.mem_cons_of_mem _ hN)
      have hsum : Matrix.PosSemidef l.sum := list_sum_posSemidef l hrest
      rw [List.sum_cons, Matrix.add_mulVec] at hv
      set a : ℂ := star v ⬝ᵥ (A *ᵥ v) with ha_def
      set b : ℂ := star v ⬝ᵥ (l.sum *ᵥ v) with hb_def
      have ha_le : (0 : ℂ) ≤ a := by
        rw [ha_def]
        exact hA.dotProduct_mulVec_nonneg v
      have hb_le : (0 : ℂ) ≤ b := by
        rw [hb_def]
        exact hsum.dotProduct_mulVec_nonneg v
      have hab : a + b = 0 := by
        rw [ha_def, hb_def, ← dotProduct_add, hv]
        simp
      rw [Complex.le_def] at ha_le hb_le
      simp only [Complex.zero_re, Complex.zero_im] at ha_le hb_le
      have hre : a.re + b.re = 0 := by
        have := congrArg Complex.re hab
        simpa using this
      have ha0 : a = 0 := by
        apply Complex.ext
        · simp only [Complex.zero_re]; linarith [ha_le.1, hb_le.1]
        · simp only [Complex.zero_im]; exact ha_le.2.symm
      have hb0 : b = 0 := by
        apply Complex.ext
        · simp only [Complex.zero_re]; linarith [ha_le.1, hb_le.1]
        · simp only [Complex.zero_im]; exact hb_le.2.symm
      have hAv : A *ᵥ v = 0 := (hA.dotProduct_mulVec_zero_iff v).mp ha0
      have hSv : l.sum *ᵥ v = 0 := (hsum.dotProduct_mulVec_zero_iff v).mp hb0
      intro M hM
      rcases List.mem_cons.mp hM with rfl | hM'
      · exact hAv
      · exact ih hrest hSv M hM'

private lemma list_sum_mulVec_zero {n : ℕ} (v : Fin n → ℂ) :
    ∀ l : List (Matrix (Fin n) (Fin n) ℂ),
      (∀ M ∈ l, M *ᵥ v = 0) → l.sum *ᵥ v = 0 := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons A l ih =>
      intro hl
      rw [List.sum_cons, Matrix.add_mulVec, hl A List.mem_cons_self,
        ih fun M hM => hl M (List.mem_cons_of_mem _ hM)]
      simp

/-- JUNK-CLOSURE (machine-checked): CPTP maps preserve support inclusion. Hence in
    `relative_entropy_monotone` the LEFT side `D_real(Φρ ‖ Φσ)` is also an honest value whenever
    the hypothesis `support_le ρ σ` holds. -/
theorem support_le_cptp {n : ℕ} (Φ : CPTPMap n) {ρ σ : DensityMatrix n}
    (h : support_le ρ σ) : support_le (Φ.apply ρ) (Φ.apply σ) := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have hv' : (Φ.kraus_ops.map (fun K => K * σ.matrix * K.conjTranspose)).sum *ᵥ v = 0 := hv
  have hσlist : ∀ M ∈ Φ.kraus_ops.map (fun K => K * σ.matrix * K.conjTranspose),
      Matrix.PosSemidef M := by
    intro M hM
    obtain ⟨K, _, rfl⟩ := List.mem_map.mp hM
    exact σ.positive.mul_mul_conjTranspose_same K
  have heach := list_psd_sum_mulVec_zero v _ hσlist hv'
  have hρlist : ∀ M ∈ Φ.kraus_ops.map (fun K => K * ρ.matrix * K.conjTranspose),
      M *ᵥ v = 0 := by
    intro M hM
    obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hM
    have hKσ : (K * σ.matrix * K.conjTranspose) *ᵥ v = 0 :=
      heach _ (List.mem_map.mpr ⟨K, hK, rfl⟩)
    set w : Fin n → ℂ := K.conjTranspose *ᵥ v with hw
    have hσw : σ.matrix *ᵥ w = 0 := by
      apply (σ.positive.dotProduct_mulVec_zero_iff w).mp
      have hstarw : star w = star v ᵥ* K := by
        rw [hw, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
      calc star w ⬝ᵥ (σ.matrix *ᵥ w)
          = (star v ᵥ* K) ⬝ᵥ (σ.matrix *ᵥ w) := by rw [hstarw]
        _ = star v ⬝ᵥ (K *ᵥ (σ.matrix *ᵥ w)) := (Matrix.dotProduct_mulVec _ K _).symm
        _ = star v ⬝ᵥ ((K * σ.matrix * K.conjTranspose) *ᵥ v) := by
            rw [hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        _ = 0 := by rw [hKσ]; simp
    have hρw : ρ.matrix *ᵥ w = 0 := by
      have hmem : w ∈ LinearMap.ker σ.matrix.mulVecLin := by
        simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hσw
      have := h hmem
      simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using this
    calc (K * ρ.matrix * K.conjTranspose) *ᵥ v
        = K *ᵥ (ρ.matrix *ᵥ (K.conjTranspose *ᵥ v)) := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = K *ᵥ (ρ.matrix *ᵥ w) := by rw [hw]
      _ = 0 := by rw [hρw, Matrix.mulVec_zero]
  exact list_sum_mulVec_zero v _ hρlist

/-- JUNK-CLOSURE (machine-checked): mixtures preserve pairwise support inclusion. Hence in the
    rescoped `relative_entropy_jointly_convex` the LEFT side is also an honest value whenever the
    two hypotheses hold — the rescoped axiom never quantifies over a junk case. -/
theorem support_le_mixture_of_support_le {n : ℕ}
    (ρ₁ ρ₂ σ₁ σ₂ : DensityMatrix n) (p : ℝ) (h_p : 0 ≤ p ∧ p ≤ 1)
    (h₁ : support_le ρ₁ σ₁) (h₂ : support_le ρ₂ σ₂) :
    support_le (density_matrix_mixture ρ₁ ρ₂ p h_p)
      (density_matrix_mixture σ₁ σ₂ p h_p) := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  rcases eq_or_lt_of_le h_p.1 with hp0 | hp_pos
  · -- p = 0: both mixtures collapse onto the second component
    have hσ : (density_matrix_mixture σ₁ σ₂ p h_p).matrix = σ₂.matrix := by
      rw [mixture_matrix_eq, ← hp0]; norm_num
    have hρ : (density_matrix_mixture ρ₁ ρ₂ p h_p).matrix = ρ₂.matrix := by
      rw [mixture_matrix_eq, ← hp0]; norm_num
    rw [hσ] at hv
    rw [hρ]
    have hmem : v ∈ LinearMap.ker σ₂.matrix.mulVecLin := by
      simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hv
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using h₂ hmem
  · rcases eq_or_lt_of_le h_p.2 with hp1 | hp_lt
    · -- p = 1: both mixtures collapse onto the first component
      have hσ : (density_matrix_mixture σ₁ σ₂ p h_p).matrix = σ₁.matrix := by
        rw [mixture_matrix_eq, hp1]; norm_num
      have hρ : (density_matrix_mixture ρ₁ ρ₂ p h_p).matrix = ρ₁.matrix := by
        rw [mixture_matrix_eq, hp1]; norm_num
      rw [hσ] at hv
      rw [hρ]
      have hmem : v ∈ LinearMap.ker σ₁.matrix.mulVecLin := by
        simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hv
      simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using h₁ hmem
    · -- 0 < p < 1: the kernel of the mixture is the intersection of the kernels
      have hq_pos : 0 < 1 - p := by linarith
      obtain ⟨h1v, h2v⟩ := mixture_ker_sub σ₁ σ₂ p h_p hp_pos hq_pos v hv
      have hρ₁v : ρ₁.matrix *ᵥ v = 0 := by
        have hmem : v ∈ LinearMap.ker σ₁.matrix.mulVecLin := by
          simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using h1v
        simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using h₁ hmem
      have hρ₂v : ρ₂.matrix *ᵥ v = 0 := by
        have hmem : v ∈ LinearMap.ker σ₂.matrix.mulVecLin := by
          simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using h2v
        simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using h₂ hmem
      show (density_matrix_mixture ρ₁ ρ₂ p h_p).matrix *ᵥ v = 0
      rw [mixture_matrix_eq, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        hρ₁v, hρ₂v]
      simp

#print axioms support_le_cptp
#print axioms support_le_mixture_of_support_le

/-- Local support inclusion is exactly physlib's `MState` kernel inclusion. -/
theorem support_le_toMState_ker {n : ℕ} {ρ σ : DensityMatrix n}
    (h : support_le ρ σ) :
    (toMState σ).M.ker ≤ (toMState ρ).M.ker := by
  intro v hv
  rw [HermitianMat.mem_ker_iff_mulVec_zero] at hv ⊢
  have hv_fun : σ.matrix.mulVec v.ofLp = 0 := by
    simpa [toMState] using hv
  have hlocal : v.ofLp ∈ LinearMap.ker σ.matrix.mulVecLin := by
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hv_fun
  have hρ := h hlocal
  have hρ_fun : ρ.matrix.mulVec v.ofLp = 0 := by
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hρ
  simpa [toMState] using hρ_fun

/-- The local finite relative entropy is the physlib trace-log expression. -/
theorem relative_entropy_real_eq_phys_inner {n : ℕ} (ρ σ : DensityMatrix n) :
    relative_entropy_real ρ σ =
      inner ℝ (toMState ρ).M ((toMState ρ).M.log - (toMState σ).M.log) := by
  unfold relative_entropy_real
  rw [HermitianMat.inner_eq_re_trace]
  simp [toMState, HermitianMat.log, matrix_log]

theorem qRelativeEnt_ne_top_of_support {n : ℕ} (ρ σ : DensityMatrix n)
    (h : support_le ρ σ) :
    𝐃(toMState ρ‖toMState σ) ≠ ⊤ := by
  have hker := support_le_toMState_ker (ρ := ρ) (σ := σ) h
  have hq := qRelativeEnt_ker (ρ := toMState ρ) (σ := toMState σ) hker
  refine ne_of_apply_ne ENNReal.toEReal ?_
  rw [hq]
  exact EReal.coe_ne_top _

/-- On local support, physlib's `qRelativeEnt` has the same real value as `relative_entropy_real`. -/
theorem qRelativeEnt_toReal_eq_relative_entropy_real {n : ℕ} (ρ σ : DensityMatrix n)
    (h : support_le ρ σ) :
    (𝐃(toMState ρ‖toMState σ)).toReal = relative_entropy_real ρ σ := by
  have hker := support_le_toMState_ker (ρ := ρ) (σ := σ) h
  have hq := qRelativeEnt_ker (ρ := toMState ρ) (σ := toMState σ) hker
  have hne := qRelativeEnt_ne_top_of_support ρ σ h
  apply EReal.coe_injective
  rw [EReal.coe_ennreal_toReal hne, hq]
  exact_mod_cast (relative_entropy_real_eq_phys_inner ρ σ).symm

/-- (finite-regime, scoped) Data-processing / monotonicity, discharged via physlib DPI. -/
theorem relative_entropy_monotone {n : ℕ}
    (Φ : CPTPMap n) (ρ σ : DensityMatrix n) (h : support_le ρ σ) :
    relative_entropy_real (Φ.apply ρ) (Φ.apply σ) ≤ relative_entropy_real ρ σ := by
  let Ψ := toPhysCPTP Φ
  have hdpi := sandwichedRenyiEntropy_DPI_eq_one
    (ρ := toMState ρ) (σ := toMState σ) (Φ := Ψ)
  change 𝐃(Ψ (toMState ρ)‖Ψ (toMState σ)) ≤ 𝐃(toMState ρ‖toMState σ) at hdpi
  rw [toPhysCPTP_apply Φ ρ, toPhysCPTP_apply Φ σ] at hdpi
  have hright_ne := qRelativeEnt_ne_top_of_support ρ σ h
  have hreal := ENNReal.toReal_mono hright_ne hdpi
  rw [qRelativeEnt_toReal_eq_relative_entropy_real
      (Φ.apply ρ) (Φ.apply σ) (support_le_cptp Φ h),
    qRelativeEnt_toReal_eq_relative_entropy_real ρ σ h] at hreal
  exact hreal

theorem relative_entropy_data_processing {n : ℕ}
    (ρ σ : DensityMatrix n) (Φ : CPTPMap n) (h : support_le ρ σ) :
    relative_entropy_real (Φ.apply ρ) (Φ.apply σ) ≤ relative_entropy_real ρ σ :=
  relative_entropy_monotone Φ ρ σ h

/-! ## The dephasing channel as a concrete CPTP map -/

/-- The fixed-basis dephasing channel: Kraus operators are the rank-one diagonal projectors
    `|i⟩⟨i|`. Its action coincides with `pinching`. -/
noncomputable def dephasing_channel (n : ℕ) : CPTPMap n :=
  { kraus_ops := List.ofFn (fun i : Fin n => Matrix.diagonal (Pi.single i (1 : ℂ)))
    completeness := by
      rw [List.map_ofFn, List.sum_ofFn]
      have hterm : ∀ i : Fin n,
          ((Matrix.diagonal (Pi.single i (1 : ℂ))).conjTranspose *
              Matrix.diagonal (Pi.single i (1 : ℂ)))
            = Matrix.diagonal (Pi.single i (1 : ℂ)) := by
        intro i
        rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      calc (∑ i : Fin n, (fun K : Matrix (Fin n) (Fin n) ℂ => K.conjTranspose * K)
              (Matrix.diagonal (Pi.single i (1 : ℂ))))
          = ∑ i : Fin n, Matrix.diagonal (Pi.single i (1 : ℂ)) :=
            Finset.sum_congr rfl (fun i _ => hterm i)
        _ = 1 := by
            ext a b
            by_cases hab : a = b
            · subst hab
              simp [Matrix.sum_apply, Pi.single_apply]
            · simp [Matrix.sum_apply, Matrix.diagonal_apply_ne _ hab,
                Matrix.one_apply_ne hab] }

/-- The dephasing channel implements `pinching`. -/
theorem dephasing_channel_apply_matrix {n : ℕ} (ρ : DensityMatrix n) :
    ((dephasing_channel n).apply ρ).matrix = (pinching ρ).matrix := by
  show kraus_sum (dephasing_channel n) ρ = Matrix.diagonal (fun i : Fin n => ρ.matrix i i)
  unfold kraus_sum dephasing_channel
  rw [List.map_ofFn, List.sum_ofFn]
  ext a b
  rw [Matrix.sum_apply]
  simp only [Function.comp_apply]
  have hterm : ∀ i : Fin n,
      ((fun K : Matrix (Fin n) (Fin n) ℂ => K * ρ.matrix * K.conjTranspose)
          (Matrix.diagonal (Pi.single i (1 : ℂ)))) a b
        = ((Pi.single i (1 : ℂ) : Fin n → ℂ) a) * ρ.matrix a b *
            ((Pi.single i (1 : ℂ) : Fin n → ℂ) b) := by
    intro i
    show (Matrix.diagonal (Pi.single i (1 : ℂ)) * ρ.matrix *
        (Matrix.diagonal (Pi.single i (1 : ℂ))).conjTranspose) a b = _
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hstar : (star (Pi.single i (1 : ℂ)) : Fin n → ℂ) b
        = (Pi.single i (1 : ℂ) : Fin n → ℂ) b := by
      rw [← Pi.single_star, star_one]
    rw [hstar]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq]
    simp [Pi.single_apply]
  · rw [Matrix.diagonal_apply_ne _ hab]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hai : a = i
    · subst hai
      have hz : (Pi.single a (1 : ℂ) : Fin n → ℂ) b = 0 := by
        simp [Ne.symm hab]
      rw [hz, mul_zero]
    · have hz : (Pi.single i (1 : ℂ) : Fin n → ℂ) a = 0 := by
        simp [hai]
      rw [hz, zero_mul, zero_mul]

#print axioms dephasing_channel_apply_matrix

/-! ## Non-vacuity witnesses and legacy audit instances (soundness audit 2026-07-02)

Each formerly open or still-axiomatized obligation gets a machine-checked instance of its
conclusion at a concrete, non-degenerate state (see the `#print axioms` lines: none of the
witnesses depends on any project axiom). This rules out the "secretly `True`-collapsed or
unsatisfiable" failure mode around the statements the operator is trusting. -/

/-- `support_le ρ (maximally_mixed n)` always holds: the maximally mixed state has full support.
    Shows the `support_le` hypotheses of the scoped axioms are satisfiable (no dead quantifier). -/
theorem support_le_maximally_mixed {n : ℕ} [NeZero n] (ρ : DensityMatrix n) :
    support_le ρ (maximally_mixed n) := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have hv' : ((n : ℂ)⁻¹) • v = 0 := by
    simpa [maximally_mixed, Matrix.smul_mulVec, Matrix.one_mulVec] using hv
  have hn : ((n : ℂ)⁻¹) ≠ 0 := by
    have hne : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
    exact inv_ne_zero hne
  have hv0 : v = 0 := by
    rcases smul_eq_zero.mp hv' with h | h
    · exact absurd h hn
    · exact h
  simp [hv0]

/-- Honest nonzero value: `D_real(ρ ‖ I/n) = log n` for any idempotent (pure-projection) ρ. -/
private lemma D_idem_maximally_mixed {n : ℕ} [NeZero n] (ρ : DensityMatrix n)
    (hidem : ρ.matrix * ρ.matrix = ρ.matrix) :
    relative_entropy_real ρ (maximally_mixed n) = Real.log n := by
  unfold relative_entropy_real
  have hcast : (((n : ℝ)⁻¹ : ℝ) : ℂ) = (n : ℂ)⁻¹ := by push_cast; ring
  have hmm : (maximally_mixed n).matrix
      = (((n : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    show ((n : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ) = _
    rw [hcast]
  rw [matrix_log_of_idempotent ρ hidem,
    matrix_log_of_smul_one (maximally_mixed n) ((n : ℝ)⁻¹) hmm]
  rw [zero_sub, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_neg,
    Matrix.trace_smul, ρ.normalized]
  rw [smul_eq_mul, mul_one, Complex.neg_re, Complex.ofReal_re, Real.log_inv, neg_neg]

private lemma mixture_self_matrix {n : ℕ} (σ : DensityMatrix n) (p : ℝ)
    (h_p : 0 ≤ p ∧ p ≤ 1) :
    (density_matrix_mixture σ σ p h_p).matrix = σ.matrix := by
  rw [mixture_matrix_eq]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- NON-VACUITY WITNESS for the rescoped `relative_entropy_jointly_convex`: at
    `ρ₁ = ρ₂ = |0⟩⟨0|`, `σ₁ = σ₂ = I/2`, `p = 1/2` the support hypotheses hold, both sides are
    the honest nonzero value `log 2`, and the conclusion holds (with equality) — proven WITHOUT
    the axiom. -/
private theorem relative_entropy_jointly_convex_witness :
    support_le ketZeroDM (maximally_mixed 2) ∧
    relative_entropy_real ketZeroDM (maximally_mixed 2) = Real.log 2 ∧
    relative_entropy_real
        (density_matrix_mixture ketZeroDM ketZeroDM (1/2) half_mem)
        (density_matrix_mixture (maximally_mixed 2) (maximally_mixed 2) (1/2) half_mem)
      ≤ 1/2 * relative_entropy_real ketZeroDM (maximally_mixed 2)
        + (1 - 1/2) * relative_entropy_real ketZeroDM (maximally_mixed 2) := by
  have hD : relative_entropy_real ketZeroDM (maximally_mixed 2) = Real.log 2 := by
    have h := D_idem_maximally_mixed ketZeroDM ketZeroDM_idem
    simpa using h
  refine ⟨support_le_maximally_mixed ketZeroDM, hD, ?_⟩
  have hL : relative_entropy_real
      (density_matrix_mixture ketZeroDM ketZeroDM (1/2) half_mem)
      (density_matrix_mixture (maximally_mixed 2) (maximally_mixed 2) (1/2) half_mem)
      = relative_entropy_real ketZeroDM (maximally_mixed 2) :=
    relative_entropy_real_congr (mixture_self_matrix ketZeroDM (1/2) half_mem)
      (mixture_self_matrix (maximally_mixed 2) (1/2) half_mem)
  rw [hL, hD]
  have hsum : (1/2 : ℝ) * Real.log 2 + (1 - 1/2) * Real.log 2 = Real.log 2 := by ring
  rw [hsum]

#print axioms relative_entropy_jointly_convex_witness

/-- The `|+⟩⟨+|` state on ℂ² (maximal coherence in the computational basis). -/
private noncomputable def ketPlusDM : DensityMatrix 2 :=
  pure_state 2 (fun _ => ((Real.sqrt (1/2) : ℝ) : ℂ)) (by
    have h : ‖((Real.sqrt (1/2) : ℝ) : ℂ)‖ ^ 2 = 1/2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal,
        Real.mul_self_sqrt (by norm_num)]
    rw [Fin.sum_univ_two, h]
    norm_num)

private lemma ketPlusDM_matrix :
    ketPlusDM.matrix = fun _ _ : Fin 2 => (1/2 : ℂ) := by
  funext i j
  show ((Real.sqrt (1/2) : ℝ) : ℂ) * star ((Real.sqrt (1/2) : ℝ) : ℂ) = (1/2 : ℂ)
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num)]
  norm_num

private lemma ketPlusDM_idem : ketPlusDM.matrix * ketPlusDM.matrix = ketPlusDM.matrix := by
  rw [ketPlusDM_matrix]
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

private lemma pinching_ketPlus_eq_pinching_mm2 :
    (pinching ketPlusDM).matrix = (pinching (maximally_mixed 2)).matrix := by
  show Matrix.diagonal _ = Matrix.diagonal _
  congr 1
  funext i
  rw [ketPlusDM_matrix]
  show (1/2 : ℂ) = ((2 : ℂ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) i i
  simp

/-- STRICT-INSTANCE WITNESS for `relative_entropy_monotone`: the dephasing channel applied to
    `(|+⟩⟨+|, I/2)` strictly contracts the relative entropy from `log 2` to `0` — the theorem's
    conclusion at a non-degenerate instance, proven independently. -/
private theorem relative_entropy_monotone_witness :
    support_le ketPlusDM (maximally_mixed 2) ∧
    relative_entropy_real ketPlusDM (maximally_mixed 2) = Real.log 2 ∧
    relative_entropy_real ((dephasing_channel 2).apply ketPlusDM)
        ((dephasing_channel 2).apply (maximally_mixed 2)) = 0 ∧
    relative_entropy_real ((dephasing_channel 2).apply ketPlusDM)
        ((dephasing_channel 2).apply (maximally_mixed 2))
      ≤ relative_entropy_real ketPlusDM (maximally_mixed 2) := by
  have hD : relative_entropy_real ketPlusDM (maximally_mixed 2) = Real.log 2 := by
    have h := D_idem_maximally_mixed ketPlusDM ketPlusDM_idem
    simpa using h
  have h0 : relative_entropy_real ((dephasing_channel 2).apply ketPlusDM)
      ((dephasing_channel 2).apply (maximally_mixed 2)) = 0 := by
    apply relative_entropy_real_eq_zero_of_matrix_eq
    rw [dephasing_channel_apply_matrix, dephasing_channel_apply_matrix,
      pinching_ketPlus_eq_pinching_mm2]
  refine ⟨support_le_maximally_mixed ketPlusDM, hD, h0, ?_⟩
  rw [h0, hD]
  exact Real.log_nonneg (by norm_num)

#print axioms relative_entropy_monotone_witness

/-! ### Witnesses for the entropy trio (subadditivity, SSA, Araki–Lieb)

Product pure states: every marginal produced by the ACTUAL `partialTrace₁/₂` definitions is again
pure, so all entropies in the axiom statements evaluate to `0` and the conclusions hold with
equality — verified end-to-end through the real partial-trace code paths. -/

/-- The Kronecker-index vector of `ψ ⊗ φ`. -/
noncomputable def prodVec {m n : ℕ} (ψ : Fin m → ℂ) (φ : Fin n → ℂ) : Fin (m * n) → ℂ :=
  fun x => ψ (finProdFinEquiv.symm x).1 * φ (finProdFinEquiv.symm x).2

lemma prodVec_norm {m n : ℕ} {ψ : Fin m → ℂ} {φ : Fin n → ℂ}
    (hψ : (∑ i, ‖ψ i‖ ^ 2) = 1) (hφ : (∑ k, ‖φ k‖ ^ 2) = 1) :
    (∑ x, ‖prodVec ψ φ x‖ ^ 2) = 1 := by
  have h : (∑ x : Fin (m * n), ‖prodVec ψ φ x‖ ^ 2)
      = ∑ p : Fin m × Fin n, ‖ψ p.1‖ ^ 2 * ‖φ p.2‖ ^ 2 := by
    rw [← Equiv.sum_comp finProdFinEquiv (fun x => ‖prodVec ψ φ x‖ ^ 2)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [prodVec, Equiv.symm_apply_apply, mul_pow]
  rw [h, Fintype.sum_prod_type]
  calc ∑ x : Fin m, ∑ y : Fin n, ‖ψ (x, y).1‖ ^ 2 * ‖φ (x, y).2‖ ^ 2
      = ∑ x : Fin m, ‖ψ x‖ ^ 2 * ∑ y : Fin n, ‖φ y‖ ^ 2 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        show ∑ y : Fin n, ‖ψ x‖ ^ 2 * ‖φ y‖ ^ 2 = ‖ψ x‖ ^ 2 * ∑ y : Fin n, ‖φ y‖ ^ 2
        rw [← Finset.mul_sum]
    _ = 1 := by
        rw [hφ]
        simp only [mul_one]
        exact hψ

/-- Tracing out the second factor of a product pure state yields the first-factor pure state —
    through the ACTUAL `partialTrace₂` definition. -/
lemma partialTrace₂_prod_pure {m n : ℕ} (ψ : Fin m → ℂ) (φ : Fin n → ℂ)
    (hφ : (∑ k, ‖φ k‖ ^ 2) = 1) :
    partialTrace₂ (fun a b => prodVec ψ φ a * star (prodVec ψ φ b))
      = fun i j => ψ i * star (ψ j) := by
  funext i j
  show ∑ k : Fin n, prodVec ψ φ (finProdFinEquiv (i, k)) *
      star (prodVec ψ φ (finProdFinEquiv (j, k))) = ψ i * star (ψ j)
  have hterm : ∀ k : Fin n,
      prodVec ψ φ (finProdFinEquiv (i, k)) * star (prodVec ψ φ (finProdFinEquiv (j, k)))
        = (ψ i * star (ψ j)) * ((‖φ k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    have hφk : φ k * star (φ k) = ((‖φ k‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc prodVec ψ φ (finProdFinEquiv (i, k)) * star (prodVec ψ φ (finProdFinEquiv (j, k)))
        = (ψ i * φ k) * star (ψ j * φ k) := by
          simp [prodVec, Equiv.symm_apply_apply]
      _ = (ψ i * star (ψ j)) * (φ k * star (φ k)) := by
          rw [star_mul']
          ring
      _ = (ψ i * star (ψ j)) * ((‖φ k‖ ^ 2 : ℝ) : ℂ) := by rw [hφk]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  have hsum : (∑ k : Fin n, ((‖φ k‖ ^ 2 : ℝ) : ℂ))
      = ((∑ k : Fin n, ‖φ k‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hsum, hφ, Complex.ofReal_one, mul_one]

/-- Tracing out the first factor of a product pure state yields the second-factor pure state —
    through the ACTUAL `partialTrace₁` definition. -/
lemma partialTrace₁_prod_pure {m n : ℕ} (ψ : Fin m → ℂ) (φ : Fin n → ℂ)
    (hψ : (∑ i, ‖ψ i‖ ^ 2) = 1) :
    partialTrace₁ (fun a b => prodVec ψ φ a * star (prodVec ψ φ b))
      = fun i j => φ i * star (φ j) := by
  funext i j
  show ∑ k : Fin m, prodVec ψ φ (finProdFinEquiv (k, i)) *
      star (prodVec ψ φ (finProdFinEquiv (k, j))) = φ i * star (φ j)
  have hterm : ∀ k : Fin m,
      prodVec ψ φ (finProdFinEquiv (k, i)) * star (prodVec ψ φ (finProdFinEquiv (k, j)))
        = (φ i * star (φ j)) * ((‖ψ k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    have hψk : ψ k * star (ψ k) = ((‖ψ k‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc prodVec ψ φ (finProdFinEquiv (k, i)) * star (prodVec ψ φ (finProdFinEquiv (k, j)))
        = (ψ k * φ i) * star (ψ k * φ j) := by
          simp [prodVec, Equiv.symm_apply_apply]
      _ = (φ i * star (φ j)) * (ψ k * star (ψ k)) := by
          rw [star_mul']
          ring
      _ = (φ i * star (φ j)) * ((‖ψ k‖ ^ 2 : ℝ) : ℂ) := by rw [hψk]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  have hsum : (∑ k : Fin m, ((‖ψ k‖ ^ 2 : ℝ) : ℂ))
      = ((∑ k : Fin m, ‖ψ k‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hsum, hψ, Complex.ofReal_one, mul_one]

/-- NON-VACUITY WITNESS for `entropy_subadditive`: for EVERY normalized product pure state the
    conclusion holds (with equality `0 ≤ 0 + 0`), computed through the actual partial traces
    and proven WITHOUT the axiom. -/
theorem entropy_subadditive_witness {nA nB : ℕ} (ψ : Fin nA → ℂ) (φ : Fin nB → ℂ)
    (hψ : (∑ i, ‖ψ i‖ ^ 2) = 1) (hφ : (∑ k, ‖φ k‖ ^ 2) = 1) :
    von_neumann_entropy (pure_state (nA * nB) (prodVec ψ φ) (prodVec_norm hψ hφ)) ≤
      von_neumann_entropy (partial_trace (pure_state (nA * nB) (prodVec ψ φ) (prodVec_norm hψ hφ)))
      + von_neumann_entropy
          (partial_trace_A (pure_state (nA * nB) (prodVec ψ φ) (prodVec_norm hψ hφ))) := by
  have hAB : von_neumann_entropy (pure_state (nA * nB) (prodVec ψ φ) (prodVec_norm hψ hφ)) = 0 :=
    entropy_pure_zero _ ⟨prodVec ψ φ, rfl⟩
  have hA : von_neumann_entropy
      (partial_trace (pure_state (nA * nB) (prodVec ψ φ) (prodVec_norm hψ hφ))) = 0 := by
    apply entropy_pure_zero
    exact ⟨ψ, partialTrace₂_prod_pure ψ φ hφ⟩
  have hB : von_neumann_entropy
      (partial_trace_A (pure_state (nA * nB) (prodVec ψ φ) (prodVec_norm hψ hφ))) = 0 := by
    apply entropy_pure_zero
    exact ⟨φ, partialTrace₁_prod_pure ψ φ hψ⟩
  rw [hAB, hA, hB]
  norm_num

#print axioms entropy_subadditive_witness

/-- NON-VACUITY WITNESS for `araki_lieb_triangle`: same family, `|0 - 0| ≤ 0` with equality. -/
theorem araki_lieb_triangle_witness {nA nB : ℕ} (ψ : Fin nA → ℂ) (φ : Fin nB → ℂ)
    (hψ : (∑ i, ‖ψ i‖ ^ 2) = 1) (hφ : (∑ k, ‖φ k‖ ^ 2) = 1) :
    |von_neumann_entropy (partial_trace (pure_state (nA * nB) (prodVec ψ φ) (prodVec_norm hψ hφ)))
      - von_neumann_entropy
          (partial_trace_A (pure_state (nA * nB) (prodVec ψ φ) (prodVec_norm hψ hφ)))|
      ≤ von_neumann_entropy (pure_state (nA * nB) (prodVec ψ φ) (prodVec_norm hψ hφ)) := by
  have hAB : von_neumann_entropy (pure_state (nA * nB) (prodVec ψ φ) (prodVec_norm hψ hφ)) = 0 :=
    entropy_pure_zero _ ⟨prodVec ψ φ, rfl⟩
  have hA : von_neumann_entropy
      (partial_trace (pure_state (nA * nB) (prodVec ψ φ) (prodVec_norm hψ hφ))) = 0 := by
    apply entropy_pure_zero
    exact ⟨ψ, partialTrace₂_prod_pure ψ φ hφ⟩
  have hB : von_neumann_entropy
      (partial_trace_A (pure_state (nA * nB) (prodVec ψ φ) (prodVec_norm hψ hφ))) = 0 := by
    apply entropy_pure_zero
    exact ⟨φ, partialTrace₁_prod_pure ψ φ hψ⟩
  rw [hAB, hA, hB]
  norm_num

#print axioms araki_lieb_triangle_witness

private lemma one_vec_norm : (∑ i : Fin 1, ‖(fun _ : Fin 1 => (1 : ℂ)) i‖ ^ 2) = 1 := by
  simp

/-- Compressions of pure states are pure (used for the `partial_trace_first` marginal). -/
private lemma partialTrace₁_pure_dim_one {n : ℕ} (v : Fin (1 * n) → ℂ) :
    partialTrace₁ (m := 1) (fun a b => v a * star (v b))
      = fun i j => v (finProdFinEquiv (0, i)) * star (v (finProdFinEquiv (0, j))) := by
  funext i j
  show ∑ k : Fin 1, v (finProdFinEquiv (k, i)) * star (v (finProdFinEquiv (k, j))) = _
  rw [Fin.sum_univ_one]

/-- NON-VACUITY WITNESS for `strong_subadditivity`: instance at `nA = 1` with an ARBITRARY
    normalized product state ψ_B ⊗ ψ_C on B⊗C. All four entropies evaluate to `0` through the
    actual `partial_trace_C / partial_trace_first / partial_trace_AC` code paths (including the
    `finCongr` reindexing), and the conclusion holds with equality — proven WITHOUT the axiom. -/
theorem strong_subadditivity_witness {nB nC : ℕ} (ψB : Fin nB → ℂ) (ψC : Fin nC → ℂ)
    (hB : (∑ i, ‖ψB i‖ ^ 2) = 1) (hC : (∑ k, ‖ψC k‖ ^ 2) = 1) :
    let ρ_ABC := pure_state (1 * nB * nC)
      (prodVec (prodVec (fun _ : Fin 1 => (1 : ℂ)) ψB) ψC)
      (prodVec_norm (prodVec_norm one_vec_norm hB) hC)
    von_neumann_entropy (partial_trace_C ρ_ABC)
        + von_neumann_entropy (partial_trace_first ρ_ABC)
      ≥ von_neumann_entropy ρ_ABC + von_neumann_entropy (partial_trace_AC ρ_ABC) := by
  intro ρ_ABC
  have hABC : von_neumann_entropy ρ_ABC = 0 :=
    entropy_pure_zero _ ⟨prodVec (prodVec (fun _ : Fin 1 => (1 : ℂ)) ψB) ψC, rfl⟩
  have hABmat : (partial_trace_C ρ_ABC).matrix
      = fun i j => prodVec (fun _ : Fin 1 => (1 : ℂ)) ψB i *
          star (prodVec (fun _ : Fin 1 => (1 : ℂ)) ψB j) :=
    partialTrace₂_prod_pure (prodVec (fun _ : Fin 1 => (1 : ℂ)) ψB) ψC hC
  have hAB : von_neumann_entropy (partial_trace_C ρ_ABC) = 0 :=
    entropy_pure_zero _ ⟨prodVec (fun _ : Fin 1 => (1 : ℂ)) ψB, hABmat⟩
  have hBC : von_neumann_entropy (partial_trace_first ρ_ABC) = 0 := by
    apply entropy_pure_zero
    refine ⟨fun i => (prodVec (prodVec (fun _ : Fin 1 => (1 : ℂ)) ψB) ψC ∘
      (finCongr (Nat.mul_assoc 1 nB nC)).symm) (finProdFinEquiv (0, i)), ?_⟩
    have heq : (partial_trace_first ρ_ABC).matrix
        = partialTrace₁ (m := 1) (fun a b =>
            (prodVec (prodVec (fun _ : Fin 1 => (1 : ℂ)) ψB) ψC ∘
              (finCongr (Nat.mul_assoc 1 nB nC)).symm) a *
            star ((prodVec (prodVec (fun _ : Fin 1 => (1 : ℂ)) ψB) ψC ∘
              (finCongr (Nat.mul_assoc 1 nB nC)).symm) b)) := rfl
    rw [heq, partialTrace₁_pure_dim_one]
  have hBmat : (partial_trace_AC ρ_ABC).matrix = fun i j => ψB i * star (ψB j) := by
    show partialTrace₁ (partial_trace_C ρ_ABC).matrix = _
    rw [hABmat]
    exact partialTrace₁_prod_pure (fun _ : Fin 1 => (1 : ℂ)) ψB one_vec_norm
  have hBonly : von_neumann_entropy (partial_trace_AC ρ_ABC) = 0 :=
    entropy_pure_zero _ ⟨ψB, hBmat⟩
  rw [hABC, hAB, hBC, hBonly]

#print axioms strong_subadditivity_witness

end Quantum
