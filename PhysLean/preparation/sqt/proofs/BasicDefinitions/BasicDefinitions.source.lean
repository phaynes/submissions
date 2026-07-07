import Proofs.MathsAxioms
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Basic Quantum Definitions

Density matrices, Hermitian/unitary operators, and helper constructions.
-/

namespace Quantum

open Matrix Complex
open scoped Matrix BigOperators ComplexOrder

/-- Positive semidefiniteness alias. -/
abbrev IsPosSemidef {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Matrix.PosSemidef M

/-- Density matrix: Hermitian, PSD, trace 1. -/
structure DensityMatrix (n : ℕ) where
  matrix : Matrix (Fin n) (Fin n) ℂ
  hermitian : matrix.conjTranspose = matrix
  positive : IsPosSemidef matrix
  normalized : matrix.trace = 1

/-- Two density matrices are equal iff their matrices are equal — the three remaining fields
    are propositions, so proof irrelevance closes the gap. Needed to state channel/partial-trace
    identities at the `DensityMatrix` level. -/
theorem DensityMatrix.matrix_ext {n : ℕ} :
    ∀ {ρ σ : DensityMatrix n}, ρ.matrix = σ.matrix → ρ = σ
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

/-- Hermitian operator. -/
structure Hermitian (n : ℕ) where
  matrix : Matrix (Fin n) (Fin n) ℂ
  hermitian : matrix.conjTranspose = matrix

/-- Unitary matrix. -/
structure UnitaryMatrix (n : ℕ) where
  matrix : Matrix (Fin n) (Fin n) ℂ
  unitary : matrix * matrix.conjTranspose = 1

-- Axioms for foundational properties to avoid heavy linear-algebra proofs.
namespace Axioms

/-- Discharged (was an axiom): |ψ⟩⟨ψ| is Hermitian — pure algebra over the star ring. -/
theorem pure_state_is_hermitian {n : ℕ} (ψ : Fin n → ℂ) (_h_norm : (∑ i, ‖ψ i‖ ^ 2) = 1) :
  Matrix.conjTranspose (fun i j : Fin n => ψ i * star (ψ j)) =
    (fun i j : Fin n => ψ i * star (ψ j)) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_mul', star_star]
  ring

/-- Discharged (was an axiom): |ψ⟩⟨ψ| = vecMulVec ψ (star ψ) is PSD. -/
theorem pure_state_is_possemidef {n : ℕ} (ψ : Fin n → ℂ) (_h_norm : (∑ i, ‖ψ i‖ ^ 2) = 1) :
  Matrix.PosSemidef (fun i j : Fin n => ψ i * star (ψ j)) := by
  have heq : (fun i j : Fin n => ψ i * star (ψ j)) = Matrix.vecMulVec ψ (star ψ) := by
    ext i j; simp [Matrix.vecMulVec_apply, Pi.star_apply]
  rw [heq]
  exact Matrix.posSemidef_vecMulVec_self_star ψ

/-- Discharged (was an axiom): tr|ψ⟩⟨ψ| = ∑‖ψᵢ‖² = 1 for a normalised vector. -/
theorem pure_state_normalized {n : ℕ} (ψ : Fin n → ℂ) (h_norm : (∑ i, ‖ψ i‖ ^ 2) = 1) :
  Matrix.trace (fun i j : Fin n => ψ i * star (ψ j)) = 1 := by
  have hdiag : Matrix.trace (fun i j : Fin n => ψ i * star (ψ j))
      = ∑ i, ψ i * star (ψ i) := by
    simp [Matrix.trace, Matrix.diag]
  have hterm : ∀ i : Fin n, ψ i * star (ψ i) = ((‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    have h := Complex.mul_conj (ψ i)
    rw [Complex.normSq_eq_norm_sq] at h
    simpa using h
  rw [hdiag]
  calc ∑ i, ψ i * star (ψ i)
      = ∑ i, ((‖ψ i‖ ^ 2 : ℝ) : ℂ) := Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    _ = 1 := by rw [h_norm]; norm_num

/-- Discharged (was an axiom): kronecker of Hermitians is Hermitian, preserved by submatrix. -/
theorem tensor_product_is_hermitian {m n : ℕ} (ρ₁ : DensityMatrix m) (ρ₂ : DensityMatrix n) :
  ((Matrix.kronecker ρ₁.matrix ρ₂.matrix).submatrix
      (finProdFinEquiv (m:=m) (n:=n)).symm (finProdFinEquiv (m:=m) (n:=n)).symm).conjTranspose =
    (Matrix.kronecker ρ₁.matrix ρ₂.matrix).submatrix
      (finProdFinEquiv (m:=m) (n:=n)).symm (finProdFinEquiv (m:=m) (n:=n)).symm := by
  have hk : (Matrix.kronecker ρ₁.matrix ρ₂.matrix).IsHermitian := by
    show (Matrix.kronecker ρ₁.matrix ρ₂.matrix).conjTranspose
        = Matrix.kronecker ρ₁.matrix ρ₂.matrix
    unfold Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, ρ₁.hermitian, ρ₂.hermitian]
  exact hk.submatrix (finProdFinEquiv (m:=m) (n:=n)).symm

/-- Discharged (was an axiom): kronecker preserves PSD; submatrix-by-equiv preserves PSD. -/
theorem tensor_product_is_possemidef {m n : ℕ} (ρ₁ : DensityMatrix m) (ρ₂ : DensityMatrix n) :
  IsPosSemidef
    ((Matrix.kronecker ρ₁.matrix ρ₂.matrix).submatrix
      (finProdFinEquiv (m:=m) (n:=n)).symm (finProdFinEquiv (m:=m) (n:=n)).symm) := by
  have hk : (Matrix.kronecker ρ₁.matrix ρ₂.matrix).PosSemidef :=
    kronecker_posSemidef ρ₁.positive ρ₂.positive
  exact (Matrix.posSemidef_submatrix_equiv (finProdFinEquiv (m:=m) (n:=n)).symm).mpr hk

/-- Discharged (was an axiom): tr(ρ₁⊗ρ₂) = tr ρ₁ · tr ρ₂ = 1, invariant under the reindex. -/
theorem tensor_product_normalized {m n : ℕ} (ρ₁ : DensityMatrix m) (ρ₂ : DensityMatrix n) :
  Matrix.trace
      ((Matrix.kronecker ρ₁.matrix ρ₂.matrix).submatrix
        (finProdFinEquiv (m:=m) (n:=n)).symm (finProdFinEquiv (m:=m) (n:=n)).symm) = 1 := by
  have h1 : Matrix.trace
      ((Matrix.kronecker ρ₁.matrix ρ₂.matrix).submatrix
        (finProdFinEquiv (m:=m) (n:=n)).symm (finProdFinEquiv (m:=m) (n:=n)).symm)
      = Matrix.trace (Matrix.kronecker ρ₁.matrix ρ₂.matrix) := by
    simpa [Matrix.reindex_apply] using
      trace_reindex (finProdFinEquiv (m:=m) (n:=n)) (Matrix.kronecker ρ₁.matrix ρ₂.matrix)
  rw [h1]
  unfold Matrix.kronecker
  rw [Matrix.trace_kronecker, ρ₁.normalized, ρ₂.normalized, one_mul]

/-- Discharged (was an axiom): partial trace of a Hermitian state is Hermitian. -/
theorem partial_trace_is_hermitian {m n : ℕ} (ρ : DensityMatrix (m * n)) :
  (partialTrace₂ ρ.matrix).conjTranspose = partialTrace₂ ρ.matrix := by
  rw [← partialTrace₂_conjTranspose, ρ.hermitian]

/-- Discharged (was an axiom): partial trace of a PSD density matrix is PSD. -/
theorem partial_trace_is_possemidef {m n : ℕ} (ρ : DensityMatrix (m * n)) :
  Matrix.PosSemidef (partialTrace₂ ρ.matrix) :=
  partialTrace₂_pos ρ.positive

/-- Discharged (was an axiom): partial trace preserves trace 1. -/
theorem partial_trace_normalized {m n : ℕ} (ρ : DensityMatrix (m * n)) :
  Matrix.trace (partialTrace₂ ρ.matrix) = 1 := by
  rw [trace_partialTrace₂, ρ.normalized]

/-- Discharged (was an axiom): trace of a Hermitian matrix is the sum of its eigenvalues. -/
theorem hermitian_trace_eq_sum_eigs {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
  (hA : A.IsHermitian) :
  A.trace = ∑ j : Fin n, Complex.ofReal (hA.eigenvalues j) := by
  simpa using hA.trace_eq_sum_eigenvalues

end Axioms

/-! ## Helper lemmas for positive semidefiniteness -/

lemma zero_posSemidef {n : ℕ} : IsPosSemidef (0 : Matrix (Fin n) (Fin n) ℂ) := by
  simpa using (Matrix.PosSemidef.zero : Matrix.PosSemidef (0 : Matrix (Fin n) (Fin n) ℂ))

lemma smul_posSemidef {n : ℕ} (c : ℝ) (M : Matrix (Fin n) (Fin n) ℂ)
    (h_pos : 0 ≤ c) (h_M : IsPosSemidef M) : IsPosSemidef (c • M) := by
  simpa using (Matrix.PosSemidef.smul (x := M) (hx := h_M) (a := c) h_pos)

lemma one_posSemidef {n : ℕ} : IsPosSemidef (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simpa using (Matrix.PosSemidef.one : Matrix.PosSemidef (1 : Matrix (Fin n) (Fin n) ℂ))

/-! ## Helper functions for quantum structures -/

def DensityMatrix.toMatrix {n : ℕ} (ρ : DensityMatrix n) : Matrix (Fin n) (Fin n) ℂ :=
  ρ.matrix

def DensityMatrix.toIsHermitian {n : ℕ} (ρ : DensityMatrix n) : ρ.matrix.IsHermitian :=
  ρ.hermitian

noncomputable def DensityMatrix.eigenvalues {n : ℕ} (ρ : DensityMatrix n) : Fin n → ℝ :=
  ρ.toIsHermitian.eigenvalues

/-- Pure state from normalized vector |ψ⟩⟨ψ| -/
noncomputable def pure_state (n : ℕ) (ψ : Fin n → ℂ) (h_norm : (∑ i, ‖ψ i‖^2) = 1) :
    DensityMatrix n :=
  let M : Matrix (Fin n) (Fin n) ℂ := fun i j => ψ i * star (ψ j)
  { matrix := M,
    hermitian := by
      have := Axioms.pure_state_is_hermitian ψ h_norm
      simpa [M] using this,
    positive := by
      have := Axioms.pure_state_is_possemidef ψ h_norm
      simpa [M] using this,
    normalized := by
      have := Axioms.pure_state_normalized ψ h_norm
      simpa [M] using this }

/-- Maximally mixed state: I/n -/
noncomputable def maximally_mixed (n : ℕ) [NeZero n] : DensityMatrix n :=
  { matrix := ((n : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ),
    hermitian := by
      simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_one],
    positive := by
      have h_nonneg : 0 ≤ ((n : ℝ)⁻¹) := by
        have : 0 < (n : ℝ) := by
          have hne : n ≠ 0 := (inferInstance : NeZero n).out
          exact_mod_cast Nat.pos_of_ne_zero hne
        have hge : 0 ≤ (n : ℝ) := le_of_lt this
        exact inv_nonneg.mpr hge
      have h_cast :
          ((n : ℂ)⁻¹ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
            ((n : ℝ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
        ext; simp
      have h_psd :
          IsPosSemidef (((n : ℝ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ)) :=
        smul_posSemidef (c := (n : ℝ)⁻¹) (M := (1 : Matrix (Fin n) (Fin n) ℂ))
          h_nonneg one_posSemidef
      -- rewrite the scalar to the ℂ-valued smul using `h_cast`
      simpa [h_cast] using h_psd,
    normalized := by
      have hn' : (n : ℂ) ≠ 0 := by
        have hne : n ≠ 0 := (inferInstance : NeZero n).out
        exact_mod_cast hne
      have htrace : Matrix.trace (1 : Matrix (Fin n) (Fin n) ℂ) = (n : ℂ) := by
        simp [Matrix.trace_one]
      have hcalc : ((n : ℂ)⁻¹) * (n : ℂ) = 1 := by
        simp [hn']
      calc
        Matrix.trace (((n : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ))
            = ((n : ℂ)⁻¹) * Matrix.trace (1 : Matrix (Fin n) (Fin n) ℂ) := by
              simp [Matrix.trace_smul]
        _ = ((n : ℂ)⁻¹) * (n : ℂ) := by simp [htrace]
        _ = 1 := hcalc }

/-- Tensor product of density matrices -/
noncomputable def tensor_product {m n : ℕ} (ρ₁ : DensityMatrix m) (ρ₂ : DensityMatrix n) :
    DensityMatrix (m * n) :=
  { matrix :=
      (Matrix.kronecker ρ₁.matrix ρ₂.matrix).submatrix
        (finProdFinEquiv (m:=m) (n:=n)).symm (finProdFinEquiv (m:=m) (n:=n)).symm,
    hermitian := by
      have := Axioms.tensor_product_is_hermitian ρ₁ ρ₂
      simpa using this,
    positive := by
      have := Axioms.tensor_product_is_possemidef ρ₁ ρ₂
      simpa using this,
    normalized := by
      have := Axioms.tensor_product_normalized ρ₁ ρ₂
      simpa using this }

/-- Partial trace over second system -/
noncomputable def partial_trace {m n : ℕ} (ρ : DensityMatrix (m * n)) : DensityMatrix m :=
  { matrix := partialTrace₂ ρ.matrix,
    hermitian := by
      have := Axioms.partial_trace_is_hermitian (m := m) (n := n) ρ
      simpa using this,
    positive := by
      exact Axioms.partial_trace_is_possemidef (m := m) (n := n) ρ,
    normalized := by
      have := Axioms.partial_trace_normalized (m := m) (n := n) ρ
      simpa using this }

/-! ## Simple helper lemmas -/

lemma Hermitian.eq_conjTranspose {n : ℕ} (H : Hermitian n) :
    H.matrix = H.matrix.conjTranspose := by exact H.hermitian.symm

lemma Hermitian.add {n : ℕ} (H₁ H₂ : Hermitian n) :
    (H₁.matrix + H₂.matrix).IsHermitian := by
  exact Matrix.IsHermitian.add H₁.hermitian H₂.hermitian

lemma Hermitian.zero_matrix_hermitian {n : ℕ} :
    (0 : Matrix (Fin n) (Fin n) ℂ).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_zero]

lemma Hermitian.one_matrix_hermitian {n : ℕ} :
    (1 : Matrix (Fin n) (Fin n) ℂ).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_one]

lemma DensityMatrix.trace_eq_one {n : ℕ} (ρ : DensityMatrix n) :
    ρ.matrix.trace = 1 := ρ.normalized

lemma DensityMatrix.is_hermitian {n : ℕ} (ρ : DensityMatrix n) :
    ρ.matrix.IsHermitian := ρ.hermitian

lemma DensityMatrix.is_psd {n : ℕ} (ρ : DensityMatrix n) :
    IsPosSemidef ρ.matrix := ρ.positive

lemma DensityMatrix.eigenvalues_eq {n : ℕ} (ρ : DensityMatrix n) :
    ρ.eigenvalues = ρ.toIsHermitian.eigenvalues := rfl

lemma Hermitian.conjTranspose_eq_self {n : ℕ} (H : Hermitian n) :
    H.matrix.conjTranspose = H.matrix := H.hermitian

/-! ## Eigenvalue Properties -/

/-- Discharged (was an axiom): a density matrix is PSD, so its eigenvalues are ≥ 0. -/
theorem eigenvalue_nonneg {n : ℕ} (ρ : DensityMatrix n) (i : Fin n) :
    0 ≤ ρ.eigenvalues i := by
  have hp : ρ.matrix.PosSemidef := ρ.positive
  simpa [DensityMatrix.eigenvalues, DensityMatrix.toIsHermitian] using hp.eigenvalues_nonneg i

lemma eigenvalue_le_one {n : ℕ} (ρ : DensityMatrix n) (i : Fin n) :
    ρ.eigenvalues i ≤ 1 := by
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
  calc
    ρ.eigenvalues i ≤ ∑ j : Fin n, ρ.eigenvalues j := by
      apply Finset.single_le_sum
      · intro j _; exact h_nonneg j
      · simp
    _ = 1 := h_sum_eq_one

end Quantum
