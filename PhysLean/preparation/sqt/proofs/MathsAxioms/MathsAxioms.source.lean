import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Star.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order

/-!
# MathsAxioms

Matrix-level placeholders for missing functional calculus and linear-algebra
operations in the pinned mathlib version. No `DensityMatrix` references here.
-/

open Matrix Complex
open scoped ComplexOrder

/-! ## Matrix logarithm / functional calculus -/

/-- Discharged (was an axiom): matrix logarithm via the continuous functional calculus.
    Proof attempt by Codex GPT-5.5 (140s). -/
noncomputable def matrix_log {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  cfc Real.log M

theorem matrix_log_hermitian {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (_h : M.conjTranspose = M) :
    (matrix_log M).conjTranspose = matrix_log M := by
  exact cfc_predicate Real.log M

/-- Discharged (was an axiom): trace cyclicity is general — holds for `matrix_log B` too. -/
theorem trace_mul_matrix_log {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (A * matrix_log B) = Matrix.trace (matrix_log B * A) :=
  Matrix.trace_mul_comm A (matrix_log B)

/-- Discharged (was an axiom): trace ∘ (A * ·) distributes over a sum — `mul_add` + `trace_add`. -/
theorem trace_mul_log_linear {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (A * (matrix_log B + matrix_log C))
      = Matrix.trace (A * matrix_log B) + Matrix.trace (A * matrix_log C) := by
  rw [Matrix.mul_add, Matrix.trace_add]

/-! ## Kronecker product and reindexing -/

/-- Discharged (was an axiom): Kronecker product preserves PSD — `Matrix.PosSemidef.kronecker`. -/
theorem kronecker_posSemidef {m n : ℕ}
    {A : Matrix (Fin m) (Fin m) ℂ} {B : Matrix (Fin n) (Fin n) ℂ} :
    A.PosSemidef → B.PosSemidef → (Matrix.kronecker A B).PosSemidef :=
  fun hA hB => Matrix.PosSemidef.kronecker hA hB

/-- Trace is invariant under reindexing by an equivalence. -/
theorem trace_reindex {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : Matrix α α ℂ) :
    Matrix.trace (Matrix.reindex e e A) = Matrix.trace A := by
  simpa [Matrix.trace, Matrix.reindex_apply] using
    (Equiv.sum_comp e.symm (fun x : α => A x x))

/-! ## Partial trace (matrix-level placeholders) -/

/-- Partial trace over the second subsystem — now a REAL definition (was an opaque axiom):
    sum over the second factor of the `m×n`-reindexed block. -/
noncomputable def partialTrace₂ {m n : ℕ}
    (ρ : Matrix (Fin (m * n)) (Fin (m * n)) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ∑ k : Fin n, ρ (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k))

/-- Discharged (was an axiom): partial trace commutes with conjugate-transpose. -/
theorem partialTrace₂_conjTranspose {m n : ℕ}
    (ρ : Matrix (Fin (m * n)) (Fin (m * n)) ℂ) :
    partialTrace₂ ρ.conjTranspose = (partialTrace₂ ρ).conjTranspose := by
  ext i j
  simp only [partialTrace₂, Matrix.conjTranspose_apply, star_sum]

/-- Discharged (was an axiom): partial trace preserves PSD. Key insight — it is a SUM of
    same-index submatrix compressions of ρ, each PSD, and PSD is closed under sum. -/
theorem partialTrace₂_pos {m n : ℕ}
    {ρ : Matrix (Fin (m * n)) (Fin (m * n)) ℂ}
    (hρ : Matrix.PosSemidef ρ) :
    Matrix.PosSemidef (partialTrace₂ ρ) := by
  have hsum : partialTrace₂ ρ
      = ∑ k : Fin n, ρ.submatrix (fun i => finProdFinEquiv (i, k)) (fun i => finProdFinEquiv (i, k)) := by
    ext i j
    simp [partialTrace₂, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hsum]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun a b ha hb => ha.add hb)
    Matrix.PosSemidef.zero ?_
  intro k _
  exact hρ.submatrix _

/-- Discharged (was an axiom): tr(partialTrace₂ ρ) = tr ρ (reindex the diagonal sum). -/
theorem trace_partialTrace₂ {m n : ℕ}
    (ρ : Matrix (Fin (m * n)) (Fin (m * n)) ℂ) :
    Matrix.trace (partialTrace₂ ρ) = Matrix.trace ρ := by
  have h : (partialTrace₂ ρ).trace
      = ∑ p : Fin m × Fin n, ρ (finProdFinEquiv p) (finProdFinEquiv p) := by
    simp only [Matrix.trace, Matrix.diag_apply, partialTrace₂]
    rw [Fintype.sum_prod_type]
  rw [h, Matrix.trace]
  simp only [Matrix.diag_apply]
  exact Fintype.sum_equiv finProdFinEquiv _ _ (fun _ => rfl)
