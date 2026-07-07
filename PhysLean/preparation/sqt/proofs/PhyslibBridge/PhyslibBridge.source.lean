import Proofs.BasicDefinitions
import Proofs.CPTPEmbedding
import Proofs.MathsAxioms
import QuantumInfo.Entropy.SSA
import QuantumInfo.Entropy.DPI
import Mathlib.Data.List.OfFn

/-!
# Bridge from the local density-matrix API to physlib mixed states

This file keeps the index-convention bridge in one place.  The local API uses
`Fin (m * n)` flattened by `finProdFinEquiv`; physlib uses product index types.
-/

namespace Quantum

open Matrix Real
open scoped BigOperators ComplexOrder

/-- Von Neumann entropy, represented spectrally. -/
noncomputable def von_neumann_entropy {n : ℕ} (ρ : DensityMatrix n) : ℝ :=
  -∑ i : Fin n,
    if ρ.eigenvalues i = 0 then 0
    else ρ.eigenvalues i * Real.log (ρ.eigenvalues i)

/-- Partial trace over the first factor, as a matrix-level primitive. -/
noncomputable def partialTrace₁ {m n : ℕ}
    (ρ : Matrix (Fin (m * n)) (Fin (m * n)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∑ k : Fin m, ρ (finProdFinEquiv (k, i)) (finProdFinEquiv (k, j))

theorem partialTrace₁_conjTranspose {m n : ℕ}
    (ρ : Matrix (Fin (m * n)) (Fin (m * n)) ℂ) :
    partialTrace₁ ρ.conjTranspose = (partialTrace₁ ρ).conjTranspose := by
  ext i j
  simp only [partialTrace₁, Matrix.conjTranspose_apply, star_sum]

theorem partialTrace₁_pos {m n : ℕ}
    {ρ : Matrix (Fin (m * n)) (Fin (m * n)) ℂ}
    (hρ : Matrix.PosSemidef ρ) :
    Matrix.PosSemidef (partialTrace₁ ρ) := by
  have hsum : partialTrace₁ ρ
      = ∑ k : Fin m,
          ρ.submatrix (fun i : Fin n => finProdFinEquiv (k, i))
            (fun i : Fin n => finProdFinEquiv (k, i)) := by
    ext i j
    simp [partialTrace₁, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hsum]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun a b ha hb => ha.add hb)
    Matrix.PosSemidef.zero ?_
  intro k _
  exact hρ.submatrix _

theorem trace_partialTrace₁ {m n : ℕ}
    (ρ : Matrix (Fin (m * n)) (Fin (m * n)) ℂ) :
    Matrix.trace (partialTrace₁ ρ) = Matrix.trace ρ := by
  have h : (partialTrace₁ ρ).trace
      = ∑ p : Fin m × Fin n, ρ (finProdFinEquiv p) (finProdFinEquiv p) := by
    simp only [Matrix.trace, Matrix.diag_apply, partialTrace₁]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
  rw [h, Matrix.trace]
  simp only [Matrix.diag_apply]
  exact Fintype.sum_equiv finProdFinEquiv _ _ (fun _ => rfl)

/-- Partial trace over subsystem A, keeping B. -/
noncomputable def partial_trace_A {nA nB : ℕ}
    (ρ : DensityMatrix (nA * nB)) : DensityMatrix nB :=
  { matrix := partialTrace₁ ρ.matrix
    hermitian := by rw [← partialTrace₁_conjTranspose, ρ.hermitian]
    positive := partialTrace₁_pos ρ.positive
    normalized := by rw [trace_partialTrace₁, ρ.normalized] }

/-- Trace out C from an `(A*B)*C`-flattened local state. -/
noncomputable def partial_trace_C {nA nB nC : ℕ} :
    DensityMatrix (nA * nB * nC) → DensityMatrix (nA * nB) := fun ρ =>
  { matrix := partialTrace₂ (m := nA * nB) (n := nC) ρ.matrix
    hermitian := by rw [← partialTrace₂_conjTranspose, ρ.hermitian]
    positive := partialTrace₂_pos ρ.positive
    normalized := by rw [trace_partialTrace₂, ρ.normalized] }

/-- Trace out A from an `(A*B)*C`-flattened local state, keeping `B*C`. -/
noncomputable def partial_trace_first {nA nB nC : ℕ} :
    DensityMatrix (nA * nB * nC) → DensityMatrix (nB * nC) := fun ρ =>
  let e := finCongr (Nat.mul_assoc nA nB nC)
  { matrix := partialTrace₁ (m := nA) (n := nB * nC) (ρ.matrix.submatrix e.symm e.symm)
    hermitian := by
      rw [← partialTrace₁_conjTranspose]
      congr 1
      exact Matrix.IsHermitian.submatrix ρ.hermitian e.symm
    positive :=
      partialTrace₁_pos ((Matrix.posSemidef_submatrix_equiv e.symm).mpr ρ.positive)
    normalized := by
      rw [trace_partialTrace₁]
      have ht : Matrix.trace (ρ.matrix.submatrix e.symm e.symm) = Matrix.trace ρ.matrix :=
        trace_reindex e ρ.matrix
      rw [ht, ρ.normalized] }

/-- Trace out A and C, keeping B. -/
noncomputable def partial_trace_AC {nA nB nC : ℕ} :
    DensityMatrix (nA * nB * nC) → DensityMatrix nB := fun ρ =>
  partial_trace_A (partial_trace_C ρ)

/-- The direct state map from the local density-matrix structure to physlib's `MState`. -/
noncomputable def toMState {n : ℕ} (ρ : DensityMatrix n) : MState (Fin n) :=
  { M := ⟨ρ.matrix, ρ.hermitian⟩
    nonneg := by
      exact HermitianMat.zero_le_iff.mpr ρ.positive
    tr := by
      rw [HermitianMat.trace_eq_one_iff]
      exact ρ.normalized }

/-- Flatten a local pair product using the project's `Fin` convention. -/
noncomputable def toMStatePair {m n : ℕ} (ρ : DensityMatrix (m * n)) :
    MState (Fin m × Fin n) :=
  (toMState ρ).relabel (finProdFinEquiv (m := m) (n := n))

/-- Flatten a right-associated product as local `((A*B)*C)` indices. -/
noncomputable def finTripleEquiv (nA nB nC : ℕ) :
    (Fin nA × Fin nB × Fin nC) ≃ Fin (nA * nB * nC) :=
  ((Equiv.prodAssoc (Fin nA) (Fin nB) (Fin nC)).symm.trans
    ((Equiv.prodCongr (finProdFinEquiv (m := nA) (n := nB)) (Equiv.refl (Fin nC))).trans
      (finProdFinEquiv (m := nA * nB) (n := nC))))

/-- The tripartite state map into physlib's right-associated product type. -/
noncomputable def toMStateTriple {nA nB nC : ℕ}
    (ρ : DensityMatrix (nA * nB * nC)) : MState (Fin nA × Fin nB × Fin nC) :=
  (toMState ρ).relabel (finTripleEquiv nA nB nC)

theorem entropy_toMState {n : ℕ} (ρ : DensityMatrix n) :
    von_neumann_entropy ρ = Sᵥₙ (toMState ρ) := by
  unfold von_neumann_entropy Sᵥₙ Hₛ H₁ MState.spectrum ProbDistribution.mk'
    DensityMatrix.eigenvalues DensityMatrix.toIsHermitian toMState
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr
  · rfl
  intro i _hi
  dsimp [ProbDistribution.prob]
  by_cases hzero : Matrix.IsHermitian.eigenvalues ρ.hermitian i = 0
  · simp [hzero, Real.negMulLog_zero]
  · simp [hzero, Real.negMulLog_eq_neg]

theorem entropy_toMStatePair {m n : ℕ} (ρ : DensityMatrix (m * n)) :
    von_neumann_entropy ρ = Sᵥₙ (toMStatePair ρ) := by
  rw [entropy_toMState]
  exact (Sᵥₙ_relabel (toMState ρ) (finProdFinEquiv (m := m) (n := n))).symm

theorem entropy_toMStateTriple {nA nB nC : ℕ}
    (ρ : DensityMatrix (nA * nB * nC)) :
    von_neumann_entropy ρ = Sᵥₙ (toMStateTriple ρ) := by
  rw [entropy_toMState]
  exact (Sᵥₙ_relabel (toMState ρ) (finTripleEquiv nA nB nC)).symm

theorem toMStatePair_traceRight {m n : ℕ} (ρ : DensityMatrix (m * n)) :
    (toMStatePair (m := m) (n := n) ρ).traceRight = toMState (partial_trace ρ) := by
  apply MState.ext_m
  ext i j
  dsimp [toMStatePair, toMState, partial_trace, partialTrace₂, Matrix.traceRight,
    MState.traceRight, MState.relabel, MState.m, HermitianMat.traceRight, HermitianMat.reindex]
  change (∑ x : Fin n, ρ.matrix (finProdFinEquiv (i, x)) (finProdFinEquiv (j, x))) =
    ∑ k : Fin n, ρ.matrix (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k))
  rfl

theorem toMStatePair_traceLeft {m n : ℕ} (ρ : DensityMatrix (m * n)) :
    (toMStatePair (m := m) (n := n) ρ).traceLeft = toMState (partial_trace_A ρ) := by
  apply MState.ext_m
  ext i j
  dsimp [toMStatePair, toMState, partial_trace_A, partialTrace₁, Matrix.traceLeft,
    MState.traceLeft, MState.relabel, MState.m, HermitianMat.traceLeft, HermitianMat.reindex]
  change (∑ x : Fin m, ρ.matrix (finProdFinEquiv (x, i)) (finProdFinEquiv (x, j))) =
    ∑ k : Fin m, ρ.matrix (finProdFinEquiv (k, i)) (finProdFinEquiv (k, j))
  rfl

private theorem mstate_assoc'_eq_relabel {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (ρ : MState (A × B × C)) :
    ρ.assoc' = ρ.relabel (Equiv.prodAssoc A B C) := by
  rfl

private lemma finTriple_left_eq_assoc {nA nB nC : ℕ}
    (a : Fin nA) (b : Fin nB) (c : Fin nC) :
    finProdFinEquiv (m := nA * nB) (n := nC)
      (finProdFinEquiv (m := nA) (n := nB) (a, b), c)
      = (finCongr (Nat.mul_assoc nA nB nC)).symm
          (finProdFinEquiv (m := nA) (n := nB * nC)
            (a, finProdFinEquiv (m := nB) (n := nC) (b, c))) := by
  ext
  simp [finProdFinEquiv]
  ring

theorem toMStateTriple_assoc'_traceRight {nA nB nC : ℕ}
    (ρ : DensityMatrix (nA * nB * nC)) :
    (toMStateTriple ρ).assoc'.traceRight = toMStatePair (partial_trace_C ρ) := by
  rw [mstate_assoc'_eq_relabel]
  apply MState.ext_m
  ext x y
  rcases x with ⟨a, b⟩
  rcases y with ⟨a', b'⟩
  dsimp [toMStateTriple, toMStatePair, toMState, partial_trace_C, partialTrace₂,
    finTripleEquiv, Matrix.traceRight, MState.traceRight,
    MState.relabel, MState.m, HermitianMat.traceRight, HermitianMat.reindex]
  change (∑ x : Fin nC,
      ρ.matrix
        (finProdFinEquiv (m := nA * nB) (n := nC) (finProdFinEquiv (m := nA) (n := nB) (a, b), x))
        (finProdFinEquiv (m := nA * nB) (n := nC) (finProdFinEquiv (m := nA) (n := nB) (a', b'), x))) =
    ∑ k : Fin nC,
      ρ.matrix
        (finProdFinEquiv (m := nA * nB) (n := nC) (finProdFinEquiv (m := nA) (n := nB) (a, b), k))
        (finProdFinEquiv (m := nA * nB) (n := nC) (finProdFinEquiv (m := nA) (n := nB) (a', b'), k))
  rfl

theorem toMStateTriple_traceLeft {nA nB nC : ℕ}
    (ρ : DensityMatrix (nA * nB * nC)) :
    (toMStateTriple ρ).traceLeft = toMStatePair (partial_trace_first ρ) := by
  apply MState.ext_m
  ext x y
  rcases x with ⟨b, c⟩
  rcases y with ⟨b', c'⟩
  dsimp [toMStateTriple, toMStatePair, toMState, partial_trace_first, partialTrace₁,
    finTripleEquiv, Matrix.traceLeft, MState.traceLeft,
    MState.relabel, MState.m, HermitianMat.traceLeft, HermitianMat.reindex]
  change (∑ a : Fin nA,
      ρ.matrix
        (finProdFinEquiv (m := nA * nB) (n := nC) (finProdFinEquiv (m := nA) (n := nB) (a, b), c))
        (finProdFinEquiv (m := nA * nB) (n := nC) (finProdFinEquiv (m := nA) (n := nB) (a, b'), c'))) =
    ∑ a : Fin nA,
      ρ.matrix
        ((finCongr (Nat.mul_assoc nA nB nC)).symm
          (finProdFinEquiv (m := nA) (n := nB * nC)
            (a, finProdFinEquiv (m := nB) (n := nC) (b, c))))
        ((finCongr (Nat.mul_assoc nA nB nC)).symm
          (finProdFinEquiv (m := nA) (n := nB * nC)
            (a, finProdFinEquiv (m := nB) (n := nC) (b', c'))))
  apply Finset.sum_congr rfl
  intro a _
  rw [finTriple_left_eq_assoc a b c, finTriple_left_eq_assoc a b' c']

theorem toMStateTriple_traceLeft_traceRight {nA nB nC : ℕ}
    (ρ : DensityMatrix (nA * nB * nC)) :
    (toMStateTriple ρ).traceLeft.traceRight = toMState (partial_trace_AC ρ) := by
  apply MState.ext_m
  ext b b'
  dsimp [toMStateTriple, toMState, partial_trace_AC, partial_trace_A, partial_trace_C,
    partialTrace₁, partialTrace₂, finTripleEquiv, Matrix.traceLeft, Matrix.traceRight,
    MState.traceLeft, MState.traceRight, MState.relabel, MState.m,
    HermitianMat.traceLeft, HermitianMat.traceRight, HermitianMat.reindex]
  change (∑ c : Fin nC, ∑ a : Fin nA,
      ρ.matrix
        (finProdFinEquiv (m := nA * nB) (n := nC) (finProdFinEquiv (m := nA) (n := nB) (a, b), c))
        (finProdFinEquiv (m := nA * nB) (n := nC) (finProdFinEquiv (m := nA) (n := nB) (a, b'), c))) =
    ∑ a : Fin nA, ∑ c : Fin nC,
      ρ.matrix
        (finProdFinEquiv (m := nA * nB) (n := nC) (finProdFinEquiv (m := nA) (n := nB) (a, b), c))
        (finProdFinEquiv (m := nA * nB) (n := nC) (finProdFinEquiv (m := nA) (n := nB) (a, b'), c))
  rw [Finset.sum_comm]

private theorem list_matrix_sum_apply {n : ℕ}
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (i j : Fin n) :
    l.sum i j = (l.map fun M => M i j).sum := by
  induction l with
  | nil => simp
  | cons M Ms ih => simp [List.sum_cons, ih]

/-- Convert the local list-of-Kraus-operators channel into physlib's bundled channel. -/
noncomputable def toPhysCPTP {n : ℕ} (Φ : CPTPMap n) :
    _root_.CPTPMap (Fin n) (Fin n) :=
  _root_.CPTPMap.of_kraus_CPTPMap
    (fun i : Fin Φ.kraus_ops.length => Φ.kraus_ops.get i)
    (by
      rw [← Φ.completeness]
      rw [← List.sum_ofFn]
      rw [List.ofFn_comp' Φ.kraus_ops.get (fun K => K.conjTranspose * K)]
      rw [List.ofFn_get])

/-- The physlib channel converted from a local channel has exactly the local Kraus action. -/
theorem toPhysCPTP_apply {n : ℕ} (Φ : CPTPMap n) (ρ : DensityMatrix n) :
    toPhysCPTP Φ (toMState ρ) = toMState (Φ.apply ρ) := by
  apply MState.ext_m
  rw [_root_.CPTPMap.mat_coe_eq_apply_mat]
  ext i j
  change (MatrixMap.of_kraus (fun i : Fin Φ.kraus_ops.length => Φ.kraus_ops.get i)
      (fun i : Fin Φ.kraus_ops.length => Φ.kraus_ops.get i) ρ.matrix) i j =
    (List.map (fun K => K * ρ.matrix * K.conjTranspose) Φ.kraus_ops).sum i j
  simp [MatrixMap.of_kraus, Matrix.sum_apply]
  rw [← List.sum_ofFn]
  rw [List.ofFn_getElem_eq_map Φ.kraus_ops
    (fun K => (K * ρ.matrix * K.conjTranspose) i j)]
  simpa [List.map_map, Function.comp_def] using
    (list_matrix_sum_apply
      (Φ.kraus_ops.map fun K => K * ρ.matrix * K.conjTranspose) i j).symm

end Quantum
