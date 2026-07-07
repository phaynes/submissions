import Proofs.CoherentFreeEnergy

/-!
# Maximum Entropy and Canonical Ensemble

Restart-wave interface for the canonical maximum-entropy story. The former
file contained proof sketches that did not compile against the current Lean and
mathlib surface; these statements are now explicit proof debt.
-/

namespace Quantum

open Matrix Real
open scoped BigOperators ComplexOrder

private lemma hermitian_eigenvalue_diagonal {n : ℕ} (H : Hermitian n) :
    Matrix.diagonal (Complex.ofReal ∘ H.toIsHermitian.eigenvalues) =
      Matrix.diagonal (fun i : Fin n => (H.toIsHermitian.eigenvalues i : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal, Function.comp_apply]
  · simp [Matrix.diagonal, hij]

private lemma hermitian_spectral_maxent {n : ℕ} (H : Hermitian n) :
    H.matrix =
      (H.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.diagonal (fun i : Fin n => (H.toIsHermitian.eigenvalues i : ℂ)) *
        star (H.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
  simpa [Matrix.mul_assoc, hermitian_eigenvalue_diagonal H] using
    H.toIsHermitian.spectral_theorem

theorem canonical_unique_max_entropy {n : ℕ} [NeZero n] (H : Hermitian n) (E : ℝ) (β : ℝ)
    (h_β : β > 0)
    (h_energy : ((canonical_state H β).matrix * H.matrix).trace.re = E) :
  ∀ ρ : DensityMatrix n,
    (ρ.matrix * H.matrix).trace.re = E →
    ρ = canonical_state H β ∨
      von_neumann_entropy ρ < von_neumann_entropy (canonical_state H β) := by
  intro ρ hρ_energy
  by_cases heq : ρ = canonical_state H β
  · exact Or.inl heq
  · right
    let γ := canonical_state H β
    have hsupp : support_le ρ γ := by
      simpa [γ] using support_le_canonical ρ H β
    have hD_nonneg : 0 ≤ relative_entropy_real ρ γ :=
      relative_entropy_real_nonneg_of_support ρ γ hsupp
    have hD_ne : relative_entropy_real ρ γ ≠ 0 := by
      intro hD0
      have hρ_eq : ρ = γ := (relative_entropy_eq_zero_iff ρ γ hsupp).mp hD0
      exact heq (by simpa [γ] using hρ_eq)
    have hD_pos : 0 < relative_entropy_real ρ γ :=
      lt_of_le_of_ne hD_nonneg (Ne.symm hD_ne)
    have hmul_pos :
        0 < β * (free_energy ρ H β - free_energy (canonical_state H β) H β) := by
      rw [← relative_entropy_gibbs_identity ρ H β h_β]
      simpa [γ] using hD_pos
    have hgap_pos : 0 < free_energy ρ H β - free_energy (canonical_state H β) H β := by
      nlinarith
    unfold free_energy at hgap_pos
    rw [hρ_energy, h_energy] at hgap_pos
    have hinv_pos : 0 < 1 / β := one_div_pos.mpr h_β
    nlinarith

theorem canonical_unique_min_free_energy {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ)
    (h_β : β > 0) :
  ∀ ρ : DensityMatrix n,
    ρ ≠ canonical_state H β →
      free_energy (canonical_state H β) H β < free_energy ρ H β := by
  intro ρ hneq
  let γ := canonical_state H β
  have hsupp : support_le ρ γ := by
    simpa [γ] using support_le_canonical ρ H β
  have hD_nonneg : 0 ≤ relative_entropy_real ρ γ :=
    relative_entropy_real_nonneg_of_support ρ γ hsupp
  have hD_ne : relative_entropy_real ρ γ ≠ 0 := by
    intro hD0
    have heq : ρ = γ := (relative_entropy_eq_zero_iff ρ γ hsupp).mp hD0
    exact hneq (by simpa [γ] using heq)
  have hD_pos : 0 < relative_entropy_real ρ γ :=
    lt_of_le_of_ne hD_nonneg (Ne.symm hD_ne)
  have hmul_pos :
      0 < β * (free_energy ρ H β - free_energy (canonical_state H β) H β) := by
    rw [← relative_entropy_gibbs_identity ρ H β h_β]
    simpa [γ] using hD_pos
  have hgap_pos : 0 < free_energy ρ H β - free_energy (canonical_state H β) H β := by
    nlinarith
  linarith

theorem canonical_commutes_with_hamiltonian {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) :
  (canonical_state H β).matrix * H.matrix =
    H.matrix * (canonical_state H β).matrix := by
  let U := H.toIsHermitian.eigenvectorUnitary
  let Dγ : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i : Fin n =>
      ((Real.exp (-β * H.toIsHermitian.eigenvalues i) /
        ∑ j : Fin n, Real.exp (-β * H.toIsHermitian.eigenvalues j) : ℝ) : ℂ))
  let DH : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i : Fin n => (H.toIsHermitian.eigenvalues i : ℂ))
  change ((U : Matrix (Fin n) (Fin n) ℂ) * Dγ *
      star (U : Matrix (Fin n) (Fin n) ℂ)) * H.matrix =
    H.matrix * ((U : Matrix (Fin n) (Fin n) ℂ) * Dγ *
      star (U : Matrix (Fin n) (Fin n) ℂ))
  have hH :
      H.matrix =
        (U : Matrix (Fin n) (Fin n) ℂ) * DH *
          star (U : Matrix (Fin n) (Fin n) ℂ) := by
    simpa [U, DH] using hermitian_spectral_maxent H
  have hdiag : Dγ * DH = DH * Dγ := by
    dsimp [Dγ, DH]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [mul_comm]
    · simp [Matrix.diagonal, hij]
  rw [hH]
  calc
    ((U : Matrix (Fin n) (Fin n) ℂ) * Dγ * star (U : Matrix (Fin n) (Fin n) ℂ)) *
          ((U : Matrix (Fin n) (Fin n) ℂ) * DH * star (U : Matrix (Fin n) (Fin n) ℂ))
        = (U : Matrix (Fin n) (Fin n) ℂ) * (Dγ * DH) *
            star (U : Matrix (Fin n) (Fin n) ℂ) := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (star (U : Matrix (Fin n) (Fin n) ℂ))
              (U : Matrix (Fin n) (Fin n) ℂ) (DH * star (U : Matrix (Fin n) (Fin n) ℂ))]
            rw [Unitary.coe_star_mul_self]
            simp
    _ = (U : Matrix (Fin n) (Fin n) ℂ) * (DH * Dγ) *
          star (U : Matrix (Fin n) (Fin n) ℂ) := by
            rw [hdiag]
    _ = ((U : Matrix (Fin n) (Fin n) ℂ) * DH * star (U : Matrix (Fin n) (Fin n) ℂ)) *
          ((U : Matrix (Fin n) (Fin n) ℂ) * Dγ * star (U : Matrix (Fin n) (Fin n) ℂ)) := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (star (U : Matrix (Fin n) (Fin n) ℂ))
              (U : Matrix (Fin n) (Fin n) ℂ) (Dγ * star (U : Matrix (Fin n) (Fin n) ℂ))]
            rw [Unitary.coe_star_mul_self]
            simp

theorem partition_function_free_energy_relation {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ)
    (h_β : β > 0) :
  Real.log (partition_function H β) =
    -β * free_energy (canonical_state H β) H β := by
  have h := canonical_free_energy_from_partition H β h_β
  have hβ_ne : β ≠ 0 := ne_of_gt h_β
  rw [h]
  field_simp [hβ_ne]

end Quantum
