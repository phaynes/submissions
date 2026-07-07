import Proofs.PinchingEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Classical Limit

Restart-wave interface for the classical limit of the SQC framework.

The previous version mixed the intended API with incomplete matrix proofs. This
file keeps the API buildable and exposes the remaining mathematical work as
explicit proof debt.
-/

namespace Quantum

open Matrix Real
open scoped BigOperators ComplexOrder

/-- A finite classical probability distribution. -/
structure ProbDist (n : ℕ) where
  prob : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ prob i
  sum_one : (Finset.univ.sum fun i => prob i) = 1

/-- Shannon entropy of a finite distribution. -/
noncomputable def shannon_entropy {n : ℕ} (p : ProbDist n) : ℝ :=
  - (Finset.univ.sum fun i => p.prob i * Real.log (p.prob i))

lemma ProbDist.prob_le_one {n : ℕ} (p : ProbDist n) (i : Fin n) :
    p.prob i ≤ 1 := by
  calc
    p.prob i ≤ Finset.univ.sum fun j : Fin n => p.prob j := by
      apply Finset.single_le_sum
      · intro j _hj
        exact p.nonneg j
      · simp
    _ = 1 := p.sum_one

/-- Discharged (was an opaque axiom) by Codex GPT-5.5 (96s): embed a distribution as a
    diagonal density matrix. -/
noncomputable def embed_prob {n : ℕ} (p : ProbDist n) : DensityMatrix n :=
  { matrix := Matrix.diagonal (fun i : Fin n => (p.prob i : ℂ))
    hermitian := by
      ext i j
      by_cases h : i = j
      · subst h
        simp [Matrix.conjTranspose, Matrix.diagonal]
      · have hji : ¬j = i := by
          intro hji
          exact h hji.symm
        simp [Matrix.conjTranspose, Matrix.diagonal, h, hji]
    positive := by
      apply Matrix.PosSemidef.diagonal
      intro i
      simpa [Complex.le_def] using p.nonneg i
    normalized := by
      calc
        Matrix.trace (Matrix.diagonal (fun i : Fin n => (p.prob i : ℂ)))
            = ∑ i : Fin n, (p.prob i : ℂ) := by
              simp [Matrix.trace]
        _ = ((∑ i : Fin n, p.prob i : ℝ) : ℂ) := by
              simp
        _ = 1 := by
              rw [p.sum_one]
              norm_num }

/-- Discharged (was an axiom) — Sonnet 5 (625s, Phase A): von Neumann entropy agrees with
    Shannon entropy on embedded distributions, via the char-poly route relating the diagonal
    matrix's eigenvalues to `p.prob` (permutation-invariance of the negMulLog sum). -/
theorem entropy_agreement {n : ℕ} (p : ProbDist n) :
  von_neumann_entropy (embed_prob p) = shannon_entropy p := by
  classical
  have hA : ((embed_prob p).matrix).IsHermitian := (embed_prob p).toIsHermitian
  have hA_diag : (embed_prob p).matrix
      = Matrix.diagonal (fun i : Fin n => (p.prob i : ℂ)) := rfl
  have hcp : (embed_prob p).matrix.charpoly
      = ∏ i : Fin n, (Polynomial.X - Polynomial.C ((p.prob i : ℂ))) := by
    rw [hA_diag]; exact Matrix.charpoly_diagonal _
  have hroots_diag :
      (embed_prob p).matrix.charpoly.roots
        = Multiset.map (fun i : Fin n => (p.prob i : ℂ)) Finset.univ.val := by
    rw [hcp, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hroots_eig :
      (embed_prob p).matrix.charpoly.roots
        = Multiset.map ((RCLike.ofReal : ℝ → ℂ) ∘ hA.eigenvalues) Finset.univ.val :=
    hA.roots_charpoly_eq_eigenvalues
  have hmap_eq :
      Multiset.map ((RCLike.ofReal : ℝ → ℂ) ∘ hA.eigenvalues) Finset.univ.val
        = Multiset.map ((RCLike.ofReal : ℝ → ℂ) ∘ p.prob) Finset.univ.val := by
    rw [← hroots_eig, hroots_diag]
    congr 1
  have hofReal_inj : Function.Injective (RCLike.ofReal : ℝ → ℂ) := RCLike.ofReal_injective
  have hmset_eq :
      Multiset.map hA.eigenvalues Finset.univ.val = Multiset.map p.prob Finset.univ.val := by
    have hcomp := hmap_eq
    rw [← Multiset.map_map, ← Multiset.map_map] at hcomp
    exact Multiset.map_injective hofReal_inj hcomp
  have hmset_eq' :
      Multiset.map (embed_prob p).eigenvalues Finset.univ.val
        = Multiset.map p.prob Finset.univ.val := by
    rw [DensityMatrix.eigenvalues_eq]; exact hmset_eq
  have hsum_negMulLog :
      ∑ i : Fin n, Real.negMulLog ((embed_prob p).eigenvalues i)
        = ∑ i : Fin n, Real.negMulLog (p.prob i) := by
    have e1 : (∑ i : Fin n, Real.negMulLog ((embed_prob p).eigenvalues i))
        = (Multiset.map Real.negMulLog
            (Multiset.map (embed_prob p).eigenvalues Finset.univ.val)).sum := by
      rw [Multiset.map_map]; rfl
    have e2 : (∑ i : Fin n, Real.negMulLog (p.prob i))
        = (Multiset.map Real.negMulLog (Multiset.map p.prob Finset.univ.val)).sum := by
      rw [Multiset.map_map]; rfl
    rw [e1, e2, hmset_eq']
  have hentropy_quantum :
      (∑ i : Fin n, Real.negMulLog ((embed_prob p).eigenvalues i))
        = von_neumann_entropy (embed_prob p) := by
    unfold von_neumann_entropy
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _hi => ?_
    by_cases hzero : (embed_prob p).eigenvalues i = 0
    · simp [hzero, Real.negMulLog_zero]
    · simp [hzero, Real.negMulLog_eq_neg]
  have hentropy_classical :
      (∑ i : Fin n, Real.negMulLog (p.prob i)) = shannon_entropy p := by
    unfold shannon_entropy
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _hi => ?_
    rw [Real.negMulLog_eq_neg]
  rw [← hentropy_quantum, ← hentropy_classical, hsum_negMulLog]

theorem shannon_entropy_nonneg {n : ℕ} (p : ProbDist n) :
  0 ≤ shannon_entropy p := by
  rw [shannon_entropy]
  rw [Left.nonneg_neg_iff]
  apply Finset.sum_nonpos
  intro i _hi
  exact mul_nonpos_of_nonneg_of_nonpos (p.nonneg i)
    (Real.log_nonpos (p.nonneg i) (p.prob_le_one i))

/-- Discharged (was an axiom) by Claude Sonnet 5 (agentic, wrote file directly): classical
    max-entropy bound via Jensen for the concave `Real.negMulLog`. -/
theorem shannon_entropy_le_log {n : ℕ} (p : ProbDist n) :
    shannon_entropy p ≤ Real.log (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    intro h
    have hn : n = 0 := by exact_mod_cast h
    subst hn
    simpa using p.sum_one
  have hjensen :
      (∑ i : Fin n, (1 / (n : ℝ)) • Real.negMulLog ((n : ℝ) * p.prob i)) ≤
        Real.negMulLog (∑ i : Fin n, (1 / (n : ℝ)) • ((n : ℝ) * p.prob i)) := by
    refine Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
      (w := fun _ : Fin n => (1 : ℝ) / n) (p := fun i => (n : ℝ) * p.prob i) ?_ ?_ ?_
    · intro i _hi; positivity
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · intro i _hi
      have := p.nonneg i
      simp only [Set.mem_Ici]
      positivity
  simp only [smul_eq_mul] at hjensen
  have hsum_arg : (∑ i : Fin n, (1 / (n : ℝ)) * ((n : ℝ) * p.prob i)) = 1 := by
    have heq : ∀ i : Fin n, (1 / (n : ℝ)) * ((n : ℝ) * p.prob i) = p.prob i := fun i => by
      field_simp
    simp_rw [heq]
    exact p.sum_one
  rw [hsum_arg, Real.negMulLog_one] at hjensen
  set C : ℝ := (1 / (n : ℝ)) * Real.negMulLog (n : ℝ) with hC
  have hexpand : ∀ i : Fin n,
      (1 / (n : ℝ)) * Real.negMulLog ((n : ℝ) * p.prob i)
        = p.prob i * C + Real.negMulLog (p.prob i) := by
    intro i
    rw [Real.negMulLog_mul (n : ℝ) (p.prob i), hC]
    field_simp
  simp_rw [hexpand] at hjensen
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, p.sum_one, one_mul] at hjensen
  have hentropy_eq : (∑ i : Fin n, Real.negMulLog (p.prob i)) = shannon_entropy p := by
    unfold shannon_entropy
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _hi => ?_
    rw [Real.negMulLog_eq_neg]
  have hC_eq : C = - Real.log (n : ℝ) := by
    rw [hC, Real.negMulLog]
    field_simp
  rw [hentropy_eq, hC_eq] at hjensen
  linarith

noncomputable def uniform_dist (n : ℕ) (hn : n > 0) : ProbDist n :=
  { prob := fun _ => 1 / (n : ℝ)
    nonneg := by
      intro _i
      positivity
    sum_one := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
      field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast ne_of_gt hn] }

theorem uniform_entropy_eq_log {n : ℕ} (hn : n > 0) :
  shannon_entropy (uniform_dist n hn) = Real.log (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  simp [shannon_entropy, uniform_dist, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hn0, one_mul]

noncomputable def deterministic_dist (n : ℕ) (k : Fin n) : ProbDist n :=
  { prob := fun i => if i = k then 1 else 0
    nonneg := by
      intro i
      by_cases h : i = k <;> simp [h]
    sum_one := by
      classical
      simp [Finset.sum_ite_eq', Finset.mem_univ] }

theorem deterministic_entropy_zero {n : ℕ} (k : Fin n) :
  shannon_entropy (deterministic_dist n k) = 0 := by
  classical
  simp [shannon_entropy, deterministic_dist, Finset.sum_ite_eq', Finset.mem_univ]

noncomputable def embed_observable {n : ℕ} (vals : Fin n → ℝ) : Hermitian n :=
  { matrix := Matrix.diagonal (fun i : Fin n => (vals i : ℂ))
    hermitian := by
      ext i j
      by_cases h : i = j
      · subst h
        simp [Matrix.conjTranspose, Matrix.diagonal]
      · have hji : ¬j = i := by
          intro hji
          exact h hji.symm
        simp [Matrix.conjTranspose, Matrix.diagonal, h, hji] }

noncomputable def expectation_value_quantum {n : ℕ}
    (ρ : DensityMatrix n) (O : Hermitian n) : ℝ :=
  ((ρ.matrix * O.matrix).trace).re

noncomputable def expectation_value_classical {n : ℕ}
    (p : ProbDist n) (vals : Fin n → ℝ) : ℝ :=
  Finset.univ.sum fun i => p.prob i * vals i

/-- Discharged (was an axiom) — Codex GPT-5.5 (44s, Phase A): diagonal×diagonal trace. -/
theorem expectation_agreement {n : ℕ} (p : ProbDist n) (vals : Fin n → ℝ) :
  expectation_value_quantum (embed_prob p) (embed_observable vals) =
    expectation_value_classical p vals := by
  simp [expectation_value_quantum, expectation_value_classical, embed_prob, embed_observable,
    Matrix.trace, Matrix.mul_apply, Matrix.diagonal]

def is_classical {n : ℕ} (ρ : DensityMatrix n) : Prop :=
  ∃ p : ProbDist n, ρ = embed_prob p

theorem classical_state_entropy {n : ℕ} (ρ : DensityMatrix n) (h : is_classical ρ) :
  ∃ p : ProbDist n, ρ = embed_prob p ∧
    von_neumann_entropy ρ = shannon_entropy p := by
  rcases h with ⟨p, rfl⟩
  exact ⟨p, rfl, entropy_agreement p⟩

theorem quantum_generalizes_classical {n : ℕ} :
    ∀ p : ProbDist n, von_neumann_entropy (embed_prob p) = shannon_entropy p :=
  fun p => entropy_agreement p

end Quantum
