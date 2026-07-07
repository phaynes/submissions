import Proofs.BasicDefinitions
import Proofs.MathsAxioms
import Mathlib.Data.List.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-!
# CPTP Maps and Stochastic Embedding

This module is the current buildable interface for completely positive
trace-preserving maps and the stochastic-to-quantum embedding. The prior file
contained extensive half-written proof bodies, including syntax that Lean could
not parse. For the restart baseline, hard obligations are made explicit as
axioms and tracked in `control/proof-debt-ledger.ndjson`.
-/

namespace Quantum

open Matrix Complex Real
open scoped BigOperators ComplexOrder

/-- A CPTP map represented by Kraus operators. -/
structure CPTPMap (n : ℕ) where
  kraus_ops : List (Matrix (Fin n) (Fin n) ℂ)
  completeness : (kraus_ops.map (fun K => K.conjTranspose * K)).sum = 1

/-- A column-stochastic real matrix. -/
def IsStochastic {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ Γ i j) ∧ (∀ j, ∑ i, Γ i j = 1)

/-- Computational-basis ket-bra operator `|i><j|`. -/
def ket_bra (n : ℕ) (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun k l => if k = i ∧ l = j then 1 else 0

/-- Kraus operator `K_ij = sqrt(Γ_ij) |i><j|`. -/
noncomputable def kraus_operator {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Matrix (Fin n) (Fin n) ℂ :=
  Complex.ofReal (√(Γ i j)) • ket_bra n i j

/-- The full Kraus family induced by a stochastic matrix. -/
noncomputable def stochastic_kraus {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) :
    List (Matrix (Fin n) (Fin n) ℂ) :=
  (Finset.univ.product Finset.univ).toList.map (fun (i, j) => kraus_operator Γ i j)

/-! ## Restart proof obligations

These are intentionally explicit. They replace non-compiling proof attempts and
are the Stage 2 proof queue, not accepted final mathematics.
-/

theorem ket_bra_conjTranspose {n : ℕ} (i j : Fin n) :
    (ket_bra n i j).conjTranspose = ket_bra n j i := by
  ext k l
  simp [ket_bra, Matrix.conjTranspose, and_comm]

/-- Discharged (was an axiom): |i⟩⟨j|·|k⟩⟨l| = δ_{jk} |i⟩⟨l|. -/
theorem ket_bra_mul {n : ℕ} (i j k l : Fin n) :
    ket_bra n i j * ket_bra n k l = if j = k then ket_bra n i l else 0 := by
  ext a b
  simp only [Matrix.mul_apply, ket_bra, Matrix.of_apply]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl]
    simp only [Matrix.of_apply]
    rw [Finset.sum_eq_single j]
    · by_cases ha : a = i <;> by_cases hb : b = l <;> simp [ha, hb]
    · intro c _ hcj; simp [hcj]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  · rw [if_neg hjk, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro c _
    rcases eq_or_ne c j with rfl | hcj
    · have : ¬ (c = k ∧ b = l) := by rintro ⟨rfl, _⟩; exact hjk rfl
      simp [this]
    · simp [hcj]

/-- Discharged (was an axiom): K†K = Γᵢⱼ |j⟩⟨j|. Compounds on `ket_bra_conjTranspose` + `ket_bra_mul`. -/
theorem kraus_operator_dagger_mul {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (h : 0 ≤ Γ i j) :
    (kraus_operator Γ i j).conjTranspose * kraus_operator Γ i j =
      Complex.ofReal (Γ i j) • ket_bra n j j := by
  unfold kraus_operator
  rw [Matrix.conjTranspose_smul, ket_bra_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
      ket_bra_mul, if_pos rfl, smul_smul]
  congr 1
  have hs : star (Complex.ofReal (√(Γ i j))) = Complex.ofReal (√(Γ i j)) := Complex.conj_ofReal _
  rw [hs, ← Complex.ofReal_mul, Real.mul_self_sqrt h]

/-- Discharged (was an axiom): ∑ⱼ |j⟩⟨j| = I. -/
theorem ket_bra_resolution_identity {n : ℕ} :
    ∑ j : Fin n, ket_bra n j j = 1 := by
  ext a b
  simp only [Matrix.sum_apply, ket_bra, Matrix.of_apply, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab; simp [Finset.sum_ite_eq]
  · simp only [if_neg hab]
    apply Finset.sum_eq_zero
    intro c _
    apply if_neg
    rintro ⟨rfl, rfl⟩
    exact hab rfl

/-- Theorem 3.1 obligation: stochastic matrices induce valid CPTP Kraus families. -/
theorem embedding_is_cptp {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (h_stoch : IsStochastic Γ) :
    ((stochastic_kraus Γ).map (fun K => K.conjTranspose * K)).sum = 1 := by
  classical
  unfold stochastic_kraus
  rw [List.map_map]
  change (List.map
      (fun p : Fin n × Fin n =>
        (kraus_operator Γ p.1 p.2).conjTranspose * kraus_operator Γ p.1 p.2)
      (Finset.univ.product Finset.univ).toList).sum = 1
  rw [Finset.sum_map_toList]
  calc
    (Finset.univ.product Finset.univ).sum
        (fun p : Fin n × Fin n =>
          (kraus_operator Γ p.1 p.2).conjTranspose * kraus_operator Γ p.1 p.2)
        = (Finset.univ.product Finset.univ).sum
            (fun p : Fin n × Fin n =>
              Complex.ofReal (Γ p.1 p.2) • ket_bra n p.2 p.2) := by
            apply Finset.sum_congr rfl
            intro p _hp
            exact kraus_operator_dagger_mul Γ p.1 p.2 (h_stoch.1 p.1 p.2)
    _ = ∑ i : Fin n, ∑ j : Fin n,
          Complex.ofReal (Γ i j) • ket_bra n j j := by
            simpa using
              (Finset.sum_product (s := (Finset.univ : Finset (Fin n)))
                (t := (Finset.univ : Finset (Fin n)))
                (f := fun p : Fin n × Fin n =>
                  Complex.ofReal (Γ p.1 p.2) • ket_bra n p.2 p.2))
    _ = ∑ j : Fin n, ∑ i : Fin n,
          Complex.ofReal (Γ i j) • ket_bra n j j := by
            rw [Finset.sum_comm]
    _ = ∑ j : Fin n,
          (∑ i : Fin n, Complex.ofReal (Γ i j)) • ket_bra n j j := by
            apply Finset.sum_congr rfl
            intro j _hj
            exact (Finset.sum_smul : (∑ i : Fin n, Complex.ofReal (Γ i j)) •
                ket_bra n j j =
              ∑ i : Fin n, Complex.ofReal (Γ i j) • ket_bra n j j).symm
    _ = ∑ j : Fin n, ket_bra n j j := by
            apply Finset.sum_congr rfl
            intro j _hj
            have hcol : (∑ i : Fin n, Complex.ofReal (Γ i j)) = 1 := by
              rw [← Complex.ofReal_sum, h_stoch.2 j]
              rfl
            rw [hcol]
            simp
    _ = 1 := ket_bra_resolution_identity

/-- Concrete quantum embedding of a classical stochastic process. -/
noncomputable def cptp_from_stochastic {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ)
    (h : IsStochastic Γ) : CPTPMap n :=
  { kraus_ops := stochastic_kraus Γ,
    completeness := embedding_is_cptp Γ h }

/-- Matrix resulting from applying all Kraus operators. -/
noncomputable def kraus_sum {n : ℕ} (Φ : CPTPMap n) (ρ : DensityMatrix n) :
    Matrix (Fin n) (Fin n) ℂ :=
  (Φ.kraus_ops.map (fun K => K * ρ.matrix * K.conjTranspose)).sum

/-- Discharged (was an axiom): the Kraus sum ∑ KρK† is Hermitian. -/
theorem kraus_sum_hermitian {n : ℕ} (Φ : CPTPMap n) (ρ : DensityMatrix n) :
    (kraus_sum Φ ρ).conjTranspose = kraus_sum Φ ρ := by
  unfold kraus_sum
  rw [Matrix.conjTranspose_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro K _
  simp only [Function.comp_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
             ρ.hermitian, mul_assoc]

/-- Discharged (was an axiom): the Kraus sum ∑ KρK† is PSD.
    Proof by Codex GPT-5.5 (75s, kernel-verified); list induction. -/
theorem kraus_sum_posSemidef {n : ℕ} (Φ : CPTPMap n) (ρ : DensityMatrix n) :
    IsPosSemidef (kraus_sum Φ ρ) := by
  unfold IsPosSemidef kraus_sum
  induction Φ.kraus_ops with
  | nil =>
      simpa using (Matrix.PosSemidef.zero :
        Matrix.PosSemidef (0 : Matrix (Fin n) (Fin n) ℂ))
  | cons K Ks ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (ρ.positive.mul_mul_conjTranspose_same K).add ih

/-- Discharged (was an axiom): CPTP maps preserve trace. Proof by Codex GPT-5.5 (190s);
    design phase picked list-induction on a list-generic trace identity, applying completeness once. -/
theorem cptp_trace_preserving {n : ℕ} (Φ : CPTPMap n) (ρ : DensityMatrix n) :
    (kraus_sum Φ ρ).trace = 1 := by
  have hlist :
      ∀ Ks : List (Matrix (Fin n) (Fin n) ℂ),
        ((Ks.map (fun K : Matrix (Fin n) (Fin n) ℂ => K * ρ.matrix * K.conjTranspose)).sum).trace =
          (((Ks.map (fun K : Matrix (Fin n) (Fin n) ℂ => K.conjTranspose * K)).sum * ρ.matrix).trace) := by
    intro Ks
    induction Ks with
    | nil =>
        simp
    | cons K Ks ih =>
        simp only [List.map_cons, List.sum_cons]
        calc
          (K * ρ.matrix * K.conjTranspose +
            (Ks.map (fun K : Matrix (Fin n) (Fin n) ℂ => K * ρ.matrix * K.conjTranspose)).sum).trace
              = (K * ρ.matrix * K.conjTranspose).trace +
                  ((Ks.map (fun K : Matrix (Fin n) (Fin n) ℂ => K * ρ.matrix * K.conjTranspose)).sum).trace := by
                    rw [Matrix.trace_add]
          _ = ((K.conjTranspose * K) * ρ.matrix).trace +
                  (((Ks.map (fun K : Matrix (Fin n) (Fin n) ℂ => K.conjTranspose * K)).sum * ρ.matrix).trace) := by
                    rw [ih]
                    congr 1
                    calc
                      (K * ρ.matrix * K.conjTranspose).trace
                          = (K.conjTranspose * (K * ρ.matrix)).trace := by
                              simpa only [mul_assoc] using
                                Matrix.trace_mul_comm (K * ρ.matrix) K.conjTranspose
                      _ = ((K.conjTranspose * K) * ρ.matrix).trace := by
                              rw [mul_assoc]
          _ = (((K.conjTranspose * K) +
                  (Ks.map (fun K : Matrix (Fin n) (Fin n) ℂ => K.conjTranspose * K)).sum) *
                  ρ.matrix).trace := by
                    rw [Matrix.add_mul, Matrix.trace_add]
  calc
    (kraus_sum Φ ρ).trace
        = (((Φ.kraus_ops.map (fun K : Matrix (Fin n) (Fin n) ℂ => K.conjTranspose * K)).sum * ρ.matrix).trace) := by
            unfold kraus_sum
            exact hlist Φ.kraus_ops
    _ = (1 * ρ.matrix).trace := by
            rw [Φ.completeness]
    _ = 1 := by
            simpa using ρ.normalized

/-- Apply a CPTP map to a density matrix. -/
noncomputable def CPTPMap.apply {n : ℕ} (Φ : CPTPMap n) (ρ : DensityMatrix n) :
    DensityMatrix n :=
  { matrix := kraus_sum Φ ρ,
    hermitian := kraus_sum_hermitian Φ ρ,
    positive := kraus_sum_posSemidef Φ ρ,
    normalized := cptp_trace_preserving Φ ρ }

/-- The unique density matrix on a 1-dimensional system: the 1×1 matrix `(1)`. -/
noncomputable def unitDM : DensityMatrix 1 :=
  { matrix := 1
    hermitian := Matrix.conjTranspose_one
    positive := one_posSemidef
    normalized := by simp [Matrix.trace_one] }

/-- Tracing out the second factor of a tensor product recovers the first factor
    (the second factor's trace-1 normalisation absorbs the sum). -/
theorem partial_trace_tensor {m n : ℕ} (ρ : DensityMatrix m) (τ : DensityMatrix n) :
    partial_trace (tensor_product ρ τ) = ρ := by
  apply DensityMatrix.matrix_ext
  show partialTrace₂ (tensor_product ρ τ).matrix = ρ.matrix
  have htr : ∑ k : Fin n, τ.matrix k k = 1 := by
    simpa [Matrix.trace, Matrix.diag] using τ.normalized
  ext i j
  have hentry : ∀ k : Fin n,
      (tensor_product ρ τ).matrix (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k))
        = ρ.matrix i j * τ.matrix k k := by
    intro k
    show (Matrix.kronecker ρ.matrix τ.matrix).submatrix
        (finProdFinEquiv (m:=m) (n:=n)).symm (finProdFinEquiv (m:=m) (n:=n)).symm
        (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k)) = _
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rfl
  calc partialTrace₂ (tensor_product ρ τ).matrix i j
      = ∑ k : Fin n,
          (tensor_product ρ τ).matrix (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k)) := rfl
    _ = ∑ k : Fin n, ρ.matrix i j * τ.matrix k k :=
        Finset.sum_congr rfl (fun k _ => hentry k)
    _ = ρ.matrix i j * ∑ k : Fin n, τ.matrix k k := by rw [← Finset.mul_sum]
    _ = ρ.matrix i j := by rw [htr, mul_one]

/-- DISCHARGED 2026-07-02 (soundness audit; was `axiom`): this statement is PROVABLE with the
    trivial witness `m = 1`, `U = I`, `σ = (Φ.apply ρ) ⊗ unitDM` — which is exactly why it was
    reclassified WEAK: the unitary `_U` is unused and `σ` is re-picked per ρ, so the statement
    does NOT capture genuine Stinespring dilation (one universal isometry dilating the map for
    ALL ρ). Proving it removes it from the trusted axiom base; the honest Stinespring statement
    `Φ.apply ρ = partial_trace (U (ρ ⊗ |0⟩⟨0|) Uᴴ)` with a universal `U` remains future work
    and must be re-introduced as a NEW, properly-cited axiom if the development ever needs it. -/
theorem stinespring_exists {n : ℕ} (Φ : CPTPMap n) :
  ∃ (m : ℕ) (_U : UnitaryMatrix (n * m)),
    ∀ ρ : DensityMatrix n,
      ∃ σ : DensityMatrix (n * m),
        Φ.apply ρ = partial_trace (m := n) (n := m) σ :=
  ⟨1, ⟨1, by simp⟩, fun ρ =>
    ⟨tensor_product (Φ.apply ρ) unitDM, (partial_trace_tensor (Φ.apply ρ) unitDM).symm⟩⟩

#print axioms stinespring_exists

/-- A CPTP map is unital when it preserves the maximally mixed state. -/
def CPTPMap.is_unital {n : ℕ} [NeZero n] (Φ : CPTPMap n) : Prop :=
  (Φ.apply (maximally_mixed n)).matrix = (maximally_mixed n).matrix

/-- A doubly stochastic CPTP map is represented here by unitality. -/
def CPTPMap.is_doubly_stochastic {n : ℕ} [NeZero n] (Φ : CPTPMap n) : Prop :=
  Φ.is_unital

/-- Discharged (was an axiom): unitality forces `∑ KKᴴ = 1`. Follows directly from
    `is_unital` at the maximally-mixed state: `∑ K(I/n)Kᴴ = I/n` scales to `∑ KKᴴ = I`
    since `n ≠ 0`, by pulling the scalar `n⁻¹` out of the Kraus sum and cancelling it. -/
theorem unital_kraus_condition {n : ℕ} [NeZero n] (Φ : CPTPMap n) :
    Φ.is_unital →
    (Φ.kraus_ops.map (fun K => K * K.conjTranspose)).sum = 1 := by
  intro h
  have hn' : (n : ℂ) ≠ 0 := by
    have hne : n ≠ 0 := (inferInstance : NeZero n).out
    exact_mod_cast hne
  have hpull :
      ∀ Ks : List (Matrix (Fin n) (Fin n) ℂ),
        (Ks.map (fun K => K * (((n : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ)) * K.conjTranspose)).sum
          = ((n : ℂ)⁻¹) • (Ks.map (fun K => K * K.conjTranspose)).sum := by
    intro Ks
    induction Ks with
    | nil => simp
    | cons K Ks ih =>
        have hK : K * (((n : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ)) * K.conjTranspose
            = ((n : ℂ)⁻¹) • (K * K.conjTranspose) := by
          rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
        simp only [List.map_cons, List.sum_cons, hK, ih, smul_add]
  have hkey :
      ((n : ℂ)⁻¹) • (Φ.kraus_ops.map (fun K => K * K.conjTranspose)).sum
        = ((n : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← hpull Φ.kraus_ops]
    simpa [CPTPMap.is_unital, CPTPMap.apply, kraus_sum, maximally_mixed] using h
  calc
    (Φ.kraus_ops.map (fun K => K * K.conjTranspose)).sum
        = (1 : ℂ) • (Φ.kraus_ops.map (fun K => K * K.conjTranspose)).sum := (one_smul _ _).symm
    _ = ((n : ℂ) * (n : ℂ)⁻¹) • (Φ.kraus_ops.map (fun K => K * K.conjTranspose)).sum := by
          rw [mul_inv_cancel₀ hn']
    _ = (n : ℂ) • (((n : ℂ)⁻¹) • (Φ.kraus_ops.map (fun K => K * K.conjTranspose)).sum) := by
          rw [smul_smul]
    _ = (n : ℂ) • (((n : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by rw [hkey]
    _ = ((n : ℂ) * (n : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ) := by rw [smul_smul]
    _ = (1 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by rw [mul_inv_cancel₀ hn']
    _ = 1 := one_smul _ _

noncomputable def CPTPMap.compose {n : ℕ} (Φ₁ Φ₂ : CPTPMap n) : CPTPMap n :=
  { kraus_ops := Φ₁.kraus_ops.flatMap (fun K₁ => Φ₂.kraus_ops.map (fun K₂ => K₂ * K₁)),
    completeness := by
      have hsandwich :
          ∀ (A B : Matrix (Fin n) (Fin n) ℂ) (Ls : List (Matrix (Fin n) (Fin n) ℂ)),
            (Ls.map (fun X => A * X * B)).sum = A * Ls.sum * B := by
        intro A B Ls
        induction Ls with
        | nil =>
            simp
        | cons X Xs ih =>
            simp only [List.map_cons, List.sum_cons]
            rw [ih]
            simp [mul_assoc, mul_add, add_mul]
      have hinner :
          ∀ K₁ : Matrix (Fin n) (Fin n) ℂ,
            (((Φ₂.kraus_ops.map (fun K₂ => K₂ * K₁)).map
                (fun K => K.conjTranspose * K)).sum) = K₁.conjTranspose * K₁ := by
        intro K₁
        calc
          (((Φ₂.kraus_ops.map (fun K₂ => K₂ * K₁)).map
              (fun K => K.conjTranspose * K)).sum)
              = (Φ₂.kraus_ops.map
                  (fun K₂ => K₁.conjTranspose * (K₂.conjTranspose * K₂) * K₁)).sum := by
                  rw [List.map_map]
                  apply congrArg List.sum
                  apply List.map_congr_left
                  intro K₂ _
                  simp [Matrix.conjTranspose_mul, mul_assoc]
          _ = K₁.conjTranspose *
                (Φ₂.kraus_ops.map (fun K₂ => K₂.conjTranspose * K₂)).sum * K₁ := by
                  change (List.map ((fun X => K₁.conjTranspose * X * K₁) ∘
                    (fun K₂ => K₂.conjTranspose * K₂)) Φ₂.kraus_ops).sum =
                      K₁.conjTranspose *
                        (Φ₂.kraus_ops.map (fun K₂ => K₂.conjTranspose * K₂)).sum * K₁
                  rw [← List.map_map]
                  exact hsandwich K₁.conjTranspose K₁
                    (Φ₂.kraus_ops.map (fun K₂ => K₂.conjTranspose * K₂))
          _ = K₁.conjTranspose * K₁ := by
                  rw [Φ₂.completeness]
                  simp
      have houter :
          ∀ Ks : List (Matrix (Fin n) (Fin n) ℂ),
            ((Ks.flatMap (fun K₁ => Φ₂.kraus_ops.map (fun K₂ => K₂ * K₁))).map
                (fun K => K.conjTranspose * K)).sum =
              (Ks.map (fun K₁ => K₁.conjTranspose * K₁)).sum := by
        intro Ks
        induction Ks with
        | nil =>
            simp
        | cons K₁ Ks ih =>
            simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
              List.sum_cons]
            rw [hinner K₁, ih]
      calc
        ((Φ₁.kraus_ops.flatMap (fun K₁ => Φ₂.kraus_ops.map (fun K₂ => K₂ * K₁))).map
            (fun K => K.conjTranspose * K)).sum
            = (Φ₁.kraus_ops.map (fun K₁ => K₁.conjTranspose * K₁)).sum := by
                exact houter Φ₁.kraus_ops
        _ = 1 := Φ₁.completeness }

/-- Identity CPTP map. -/
noncomputable def CPTPMap.id (n : ℕ) : CPTPMap n :=
  { kraus_ops := [1],
    completeness := by
      simp [Matrix.conjTranspose_one] }

theorem CPTPMap.id_apply {n : ℕ} (ρ : DensityMatrix n) :
    (CPTPMap.id n).apply ρ = ρ := by
  cases ρ
  simp [CPTPMap.apply, CPTPMap.id, kraus_sum]

theorem CPTPMap.id_unital {n : ℕ} [NeZero n] : (CPTPMap.id n).is_unital := by
  unfold CPTPMap.is_unital
  rw [CPTPMap.id_apply]

theorem CPTPMap.id_single_kraus {n : ℕ} :
    (CPTPMap.id n).kraus_ops = [1] := by
  rfl

/-- Discharged (was an axiom): tr(U M Uᴴ) = tr M via trace cyclicity + UᴴU = 1. -/
theorem trace_unitary_conj {n : ℕ} (U : UnitaryMatrix n) (M : Matrix (Fin n) (Fin n) ℂ) :
    (U.matrix * M * U.matrix.conjTranspose).trace = M.trace := by
  have hUU : U.matrix.conjTranspose * U.matrix = 1 := mul_eq_one_comm.mp U.unitary
  calc (U.matrix * M * U.matrix.conjTranspose).trace
      = (U.matrix.conjTranspose * (U.matrix * M)).trace := by rw [Matrix.trace_mul_comm]
    _ = (U.matrix.conjTranspose * U.matrix * M).trace := by rw [← Matrix.mul_assoc]
    _ = ((1 : Matrix (Fin n) (Fin n) ℂ) * M).trace := by rw [hUU]
    _ = M.trace := by rw [Matrix.one_mul]

theorem kraus_preserves_hermitian {n : ℕ} (K M : Matrix (Fin n) (Fin n) ℂ)
    (h : M.conjTranspose = M) :
    (K * M * K.conjTranspose).conjTranspose = K * M * K.conjTranspose := by
  simp [Matrix.conjTranspose_mul, h, mul_assoc]

/-- Discharged (was an axiom): product of column-stochastic matrices is column-stochastic.
    Proof by Codex GPT-5.5 (117s, kernel-verified); calc-style. -/
theorem mul_stochastic {n : ℕ} (Γ₁ Γ₂ : Matrix (Fin n) (Fin n) ℝ)
    (h₁ : IsStochastic Γ₁) (h₂ : IsStochastic Γ₂) :
    IsStochastic (Γ₂ * Γ₁) := by
  constructor
  · intro i j
    simp only [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (h₂.1 i k) (h₁.1 k j)
  · intro j
    calc
      ∑ i, (Γ₂ * Γ₁) i j
          = ∑ i, ∑ k, Γ₂ i k * Γ₁ k j := by simp [Matrix.mul_apply]
      _ = ∑ k, ∑ i, Γ₂ i k * Γ₁ k j := by rw [Finset.sum_comm]
      _ = ∑ k, (∑ i, Γ₂ i k) * Γ₁ k j := by
            apply Finset.sum_congr rfl; intro k _; rw [Finset.sum_mul]
      _ = ∑ k, Γ₁ k j := by simp [h₂.2]
      _ = 1 := h₁.2 j

/-- Discharged (was an axiom) — Codex GPT-5.5 (433s, Phase A): functoriality of the
    stochastic→quantum embedding, via a per-entry formula for the embedded channel's action. -/
theorem embedding_preserves_composition {n : ℕ}
    (Γ₁ Γ₂ : Matrix (Fin n) (Fin n) ℝ)
    (h₁ : IsStochastic Γ₁) (h₂ : IsStochastic Γ₂)
    (ρ : DensityMatrix n) :
    (cptp_from_stochastic (Γ₂ * Γ₁) (mul_stochastic Γ₁ Γ₂ h₁ h₂)).apply ρ =
    (cptp_from_stochastic Γ₂ h₂).apply ((cptp_from_stochastic Γ₁ h₁).apply ρ) := by
  have h_apply_matrix : ∀ (Γ : Matrix (Fin n) (Fin n) ℝ) (h : IsStochastic Γ)
      (σ : DensityMatrix n) (a b : Fin n),
      ((cptp_from_stochastic Γ h).apply σ).matrix a b =
        if a = b then ∑ j : Fin n, Complex.ofReal (Γ a j) * σ.matrix j j else 0 := by
    intro Γ h σ a b
    have hkb : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n),
        ket_bra n i j * M * ket_bra n j i = M j j • ket_bra n i i := by
      intro M i j
      ext x y
      by_cases hxi : x = i <;> by_cases hyi : y = i <;>
        simp [Matrix.mul_apply, ket_bra, hxi, hyi]
    have hterm : ∀ i j : Fin n,
        kraus_operator Γ i j * σ.matrix * (kraus_operator Γ i j).conjTranspose =
          (Complex.ofReal (Γ i j) * σ.matrix j j) • ket_bra n i i := by
      intro i j
      unfold kraus_operator
      rw [Matrix.conjTranspose_smul, ket_bra_conjTranspose]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [hkb σ.matrix i j, smul_smul]
      congr 1
      have hs : star (Complex.ofReal (√(Γ i j))) = Complex.ofReal (√(Γ i j)) := Complex.conj_ofReal _
      rw [hs, ← Complex.ofReal_mul, Real.mul_self_sqrt (h.1 i j)]
    change (kraus_sum (cptp_from_stochastic Γ h) σ) a b =
        if a = b then ∑ j : Fin n, ↑(Γ a j) * σ.matrix j j else 0
    unfold cptp_from_stochastic kraus_sum stochastic_kraus
    rw [List.map_map]
    change (List.map
        (fun p : Fin n × Fin n =>
          kraus_operator Γ p.1 p.2 * σ.matrix * (kraus_operator Γ p.1 p.2).conjTranspose)
        (Finset.univ.product Finset.univ).toList).sum a b =
          if a = b then ∑ j : Fin n, ↑(Γ a j) * σ.matrix j j else 0
    rw [Finset.sum_map_toList]
    simp only [Matrix.sum_apply]
    calc
      ∑ p ∈ Finset.univ.product Finset.univ,
          (kraus_operator Γ p.1 p.2 * σ.matrix * (kraus_operator Γ p.1 p.2).conjTranspose) a b
          = ∑ p ∈ Finset.univ.product Finset.univ,
              (((Complex.ofReal (Γ p.1 p.2) * σ.matrix p.2 p.2) • ket_bra n p.1 p.1) a b) := by
              apply Finset.sum_congr rfl
              intro p _hp
              rw [hterm p.1 p.2]
      _ = ∑ i : Fin n, ∑ j : Fin n,
              (((Complex.ofReal (Γ i j) * σ.matrix j j) • ket_bra n i i) a b) := by
              simpa using
                (Finset.sum_product (s := (Finset.univ : Finset (Fin n)))
                  (t := (Finset.univ : Finset (Fin n)))
                  (f := fun p : Fin n × Fin n =>
                    (((Complex.ofReal (Γ p.1 p.2) * σ.matrix p.2 p.2) • ket_bra n p.1 p.1) a b)))
      _ = if a = b then ∑ j : Fin n, ↑(Γ a j) * σ.matrix j j else 0 := by
              by_cases hab : a = b
              · subst hab
                simp [ket_bra]
              · have hzero : ∀ i : Fin n,
                    (∑ j : Fin n, (((Complex.ofReal (Γ i j) * σ.matrix j j) • ket_bra n i i) a b)) = 0 := by
                  intro i
                  by_cases hai : a = i
                  · by_cases hbi : b = i
                    · exact (hab (hai.trans hbi.symm)).elim
                    · simp [ket_bra, hai, hbi]
                  · simp [ket_bra, hai]
                rw [if_neg hab]
                apply Finset.sum_eq_zero
                intro i _hi
                exact hzero i
  have hmatrix :
      ((cptp_from_stochastic (Γ₂ * Γ₁) (mul_stochastic Γ₁ Γ₂ h₁ h₂)).apply ρ).matrix =
      ((cptp_from_stochastic Γ₂ h₂).apply ((cptp_from_stochastic Γ₁ h₁).apply ρ)).matrix := by
    ext a b
    rw [h_apply_matrix (Γ₂ * Γ₁) (mul_stochastic Γ₁ Γ₂ h₁ h₂) ρ a b,
      h_apply_matrix Γ₂ h₂ ((cptp_from_stochastic Γ₁ h₁).apply ρ) a b]
    by_cases hab : a = b
    · subst b
      simp only [if_true]
      calc
        ∑ j : Fin n, ↑((Γ₂ * Γ₁) a j) * ρ.matrix j j
            = ∑ j : Fin n, (∑ k : Fin n, ↑(Γ₂ a k) * ↑(Γ₁ k j)) * ρ.matrix j j := by
                apply Finset.sum_congr rfl
                intro j _hj
                rw [Matrix.mul_apply, Complex.ofReal_sum]
                simp only [Complex.ofReal_mul]
        _ = ∑ j : Fin n, ∑ k : Fin n, (↑(Γ₂ a k) * ↑(Γ₁ k j)) * ρ.matrix j j := by
                apply Finset.sum_congr rfl
                intro j _hj
                rw [Finset.sum_mul]
        _ = ∑ k : Fin n, ∑ j : Fin n, (↑(Γ₂ a k) * ↑(Γ₁ k j)) * ρ.matrix j j := by
                rw [Finset.sum_comm]
        _ = ∑ k : Fin n, ↑(Γ₂ a k) * (∑ j : Fin n, ↑(Γ₁ k j) * ρ.matrix j j) := by
                apply Finset.sum_congr rfl
                intro k _hk
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _hj
                ring
        _ = ∑ k : Fin n, ↑(Γ₂ a k) * ((cptp_from_stochastic Γ₁ h₁).apply ρ).matrix k k := by
                apply Finset.sum_congr rfl
                intro k _hk
                rw [h_apply_matrix Γ₁ h₁ ρ k k]
                simp
    · simp [hab]
  have hdensity : ∀ {A B : DensityMatrix n}, A.matrix = B.matrix → A = B := by
    intro A B h
    cases A
    cases B
    simp at h
    subst h
    simp
  exact hdensity hmatrix

end Quantum
