import Proofs.PinchingEntropy
import Proofs.CPTPEmbedding
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Data.Complex.BigOperators

/-!
# Free Energy and Coherence

Restart-wave interface for canonical states, free energy, and relative
coherence. The difficult analytic and variational facts are explicit axioms
until they can be retired by focused proof tasks.
-/

namespace Quantum

open Matrix Real
open scoped BigOperators ComplexOrder

/-- Helmholtz free energy `F = Tr(ρH) - β⁻¹ S(ρ)`. -/
noncomputable def free_energy {n : ℕ}
    (ρ : DensityMatrix n) (H : Hermitian n) (β : ℝ) : ℝ :=
  ((ρ.matrix * H.matrix).trace).re - (1 / β) * von_neumann_entropy ρ

/-- Partition function for the canonical ensemble `Z = Re(Tr(exp(-βH)))`.
    Discharged (was an axiom) by Codex GPT-5.5 (134s, design phase: located NormedSpace.exp). -/
noncomputable def partition_function {n : ℕ} (H : Hermitian n) (β : ℝ) : ℝ :=
  (Matrix.trace (NormedSpace.exp (-(β : ℂ) • H.matrix))).re

/-- `H`'s Hermitian matrix, retyped so eigenbasis dot-notation (`.eigenvectorUnitary`, etc.)
    resolves against `Matrix.IsHermitian`. -/
def Hermitian.toIsHermitian {n : ℕ} (H : Hermitian n) : H.matrix.IsHermitian :=
  H.hermitian

private lemma density_eigenvalue_diagonal {n : ℕ} (ρ : DensityMatrix n) :
    Matrix.diagonal (Complex.ofReal ∘ ρ.toIsHermitian.eigenvalues) =
      Matrix.diagonal (fun i : Fin n => (ρ.eigenvalues i : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal, DensityMatrix.eigenvalues, Function.comp_apply]
  · simp [Matrix.diagonal, hij]

private lemma density_spectral_cfe {n : ℕ} (ρ : DensityMatrix n) :
    ρ.matrix =
      (ρ.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.diagonal (fun i : Fin n => (ρ.eigenvalues i : ℂ)) *
        star (ρ.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
  simpa [DensityMatrix.eigenvalues, Matrix.mul_assoc, density_eigenvalue_diagonal ρ] using
    ρ.toIsHermitian.spectral_theorem

private lemma hermitian_eigenvalue_diagonal {n : ℕ} (H : Hermitian n) :
    Matrix.diagonal (Complex.ofReal ∘ H.toIsHermitian.eigenvalues) =
      Matrix.diagonal (fun i : Fin n => (H.toIsHermitian.eigenvalues i : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal, Function.comp_apply]
  · simp [Matrix.diagonal, hij]

private lemma hermitian_spectral_cfe {n : ℕ} (H : Hermitian n) :
    H.matrix =
      (H.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.diagonal (fun i : Fin n => (H.toIsHermitian.eigenvalues i : ℂ)) *
        star (H.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
  simpa [Matrix.mul_assoc, hermitian_eigenvalue_diagonal H] using
    H.toIsHermitian.spectral_theorem

/-- The partition function is strictly positive: a finite sum of `Real.exp` values over a
    nonempty index type. -/
private lemma canonical_partition_pos {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) :
    0 < ∑ i : Fin n, Real.exp (-β * H.toIsHermitian.eigenvalues i) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

/-- Conjugating by a unitary matrix leaves the trace unchanged. -/
private lemma canonical_trace_unitary_conj {n : ℕ}
    (V : Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace ((V : Matrix (Fin n) (Fin n) ℂ) * X * star (V : Matrix (Fin n) (Fin n) ℂ))
      = Matrix.trace X := by
  calc
    Matrix.trace ((V : Matrix (Fin n) (Fin n) ℂ) * X * star (V : Matrix (Fin n) (Fin n) ℂ))
        = Matrix.trace (star (V : Matrix (Fin n) (Fin n) ℂ) *
            ((V : Matrix (Fin n) (Fin n) ℂ) * X)) := by
          rw [Matrix.trace_mul_comm]
    _ = Matrix.trace X := by
          rw [← Matrix.mul_assoc, Unitary.coe_star_mul_self, one_mul]

/-- The Gibbs weight `wᵢ = exp(-βμᵢ)/Z` for eigenvalue `μᵢ` of `H`. -/
private noncomputable def canonical_weight {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ)
    (i : Fin n) : ℝ :=
  Real.exp (-β * H.toIsHermitian.eigenvalues i) / ∑ j : Fin n,
    Real.exp (-β * H.toIsHermitian.eigenvalues j)

private lemma canonical_weight_pos {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) (i : Fin n) :
    0 < canonical_weight H β i :=
  div_pos (Real.exp_pos _) (canonical_partition_pos H β)

private lemma canonical_weight_sum {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) :
    ∑ i : Fin n, canonical_weight H β i = 1 := by
  have hZ := canonical_partition_pos H β
  unfold canonical_weight
  rw [← Finset.sum_div, div_self hZ.ne']

/-- The Gibbs matrix `V · diag(w) · V†`, built in the eigenbasis of `H`. -/
private noncomputable def canonical_matrix {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (H.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
    Matrix.diagonal (fun i : Fin n => (canonical_weight H β i : ℂ)) *
    star (H.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)

/-- Discharged (was an axiom): the Gibbs matrix is PosDef — its weights are strictly positive
    reals, so the diagonal factor is PosDef, and conjugation by the (unit, hence injective)
    eigenbasis unitary preserves PosDef. -/
private lemma canonical_matrix_posDef {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) :
    (canonical_matrix H β).PosDef := by
  classical
  have hDpos : ∀ i : Fin n, (0 : ℂ) < (canonical_weight H β i : ℂ) := by
    intro i
    exact_mod_cast canonical_weight_pos H β i
  have hD : (Matrix.diagonal (fun i : Fin n => (canonical_weight H β i : ℂ))).PosDef :=
    Matrix.PosDef.diagonal hDpos
  have hVinj : Function.Injective
      (H.toIsHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).vecMul := by
    rw [Matrix.vecMul_injective_iff_isUnit, ← Unitary.val_toUnits_apply]
    exact Units.isUnit _
  exact hD.mul_mul_conjTranspose_same hVinj

/-- Discharged (was an axiom): the Gibbs matrix has trace 1 — conjugation by a unitary preserves
    trace, and the Gibbs weights sum to 1 by construction (`Z / Z = 1`). -/
private lemma canonical_matrix_trace {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) :
    Matrix.trace (canonical_matrix H β) = 1 := by
  have htrace : Matrix.trace (canonical_matrix H β) =
      Matrix.trace (Matrix.diagonal (fun i : Fin n => (canonical_weight H β i : ℂ))) := by
    unfold canonical_matrix
    exact canonical_trace_unitary_conj _ _
  rw [htrace, Matrix.trace_diagonal, ← Complex.ofReal_sum, canonical_weight_sum,
    Complex.ofReal_one]

/-- Gibbs/canonical density matrix for Hamiltonian `H` and inverse temperature `β`, constructed
    spectrally as `exp(-βH)/Z` in the eigenbasis of `H`. Discharged (was an axiom). -/
noncomputable def canonical_state {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) : DensityMatrix n :=
  { matrix := canonical_matrix H β,
    hermitian := (canonical_matrix_posDef H β).isHermitian,
    positive := (canonical_matrix_posDef H β).posSemidef,
    normalized := canonical_matrix_trace H β }

/-- Discharged (was an axiom): the Gibbs state `exp(-βH)/Z` has strictly positive eigenvalues,
    hence is PosDef. -/
theorem canonical_state_posDef {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) :
    (canonical_state H β).matrix.PosDef :=
  canonical_matrix_posDef H β

/-- Every state has support inside a PosDef canonical state (whose kernel is `⊥`). -/
theorem support_le_canonical {n : ℕ} [NeZero n] (ρ : DensityMatrix n) (H : Hermitian n) (β : ℝ) :
    support_le ρ (canonical_state H β) := by
  have hpd := canonical_state_posDef H β
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have hv0 : v = 0 := by
    by_contra hne
    have hpos := hpd.dotProduct_mulVec_pos hne
    rw [hv] at hpos
    simp at hpos
  simp [hv0]

/-- The Gibbs matrix is the continuous functional calculus of `H` under the Gibbs weight function
    `x ↦ exp(-βx)/Z` — same eigenbasis `V`, so no eigenbasis-matching issue arises. -/
private lemma canonical_matrix_eq_cfc {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) :
    canonical_matrix H β =
      cfc (fun x : ℝ => Real.exp (-β * x) /
        ∑ j : Fin n, Real.exp (-β * H.toIsHermitian.eigenvalues j)) H.matrix := by
  rw [Matrix.IsHermitian.cfc_eq H.toIsHermitian]
  rfl

/-- Crux lemma: `log` of the Gibbs matrix is affine in `H`, via the composition property of the
    continuous functional calculus (`log ∘ (exp(-β·)/Z) = -β· - log Z` on the reals). -/
private lemma canonical_matrix_log {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) :
    matrix_log (canonical_matrix H β) =
      -(β : ℂ) • H.matrix -
        (Real.log (∑ j : Fin n, Real.exp (-β * H.toIsHermitian.eigenvalues j)) : ℂ) • 1 := by
  set Z := ∑ j : Fin n, Real.exp (-β * H.toIsHermitian.eigenvalues j) with hZdef
  have hZpos : 0 < Z := canonical_partition_pos H β
  have hspec : (spectrum ℝ H.matrix).Finite := by
    rw [H.toIsHermitian.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  have hHsa : IsSelfAdjoint H.matrix := H.toIsHermitian
  rw [matrix_log, canonical_matrix_eq_cfc H β,
    ← cfc_comp Real.log (fun x : ℝ => Real.exp (-β * x) / Z) H.matrix (ha := hHsa)
      (hg := hspec.image _ |>.continuousOn _) (hf := hspec.continuousOn _)]
  have hfun : (Real.log ∘ fun x : ℝ => Real.exp (-β * x) / Z) = fun x => -β * x - Real.log Z := by
    funext x
    simp [Function.comp, Real.log_div (Real.exp_ne_zero _) hZpos.ne', Real.log_exp]
  rw [hfun, cfc_sub (fun x : ℝ => -β * x) (fun _ : ℝ => Real.log Z) H.matrix
    (hf := hspec.continuousOn _) (hg := hspec.continuousOn _),
    cfc_const_mul_id (-β) H.matrix hHsa, cfc_const (Real.log Z) H.matrix hHsa,
    Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_smul ℂ (-β) H.matrix,
    ← IsScalarTower.algebraMap_smul ℂ (Real.log Z) (1 : Matrix (Fin n) (Fin n) ℂ)]
  norm_cast

/-- `Tr(ρ log ρ)` (real part) is minus the von Neumann entropy — same diagonal-conjugation idiom
    as the crux lemma, applied to `ρ`'s own eigenbasis. -/
private lemma trace_self_log_eq_neg_entropy {n : ℕ} (ρ : DensityMatrix n) :
    (Matrix.trace (ρ.matrix * matrix_log ρ.matrix)).re = -von_neumann_entropy ρ := by
  set U := ρ.toIsHermitian.eigenvectorUnitary
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i : Fin n => (ρ.eigenvalues i : ℂ))
    with hDdef
  set L : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i : Fin n => (Real.log (ρ.eigenvalues i) : ℂ)) with hLdef
  have hρ : ρ.matrix = (U : Matrix (Fin n) (Fin n) ℂ) * D * star (U : Matrix (Fin n) (Fin n) ℂ) := by
    simpa [U, hDdef] using density_spectral_cfe ρ
  have hlog : matrix_log ρ.matrix =
      (U : Matrix (Fin n) (Fin n) ℂ) * L * star (U : Matrix (Fin n) (Fin n) ℂ) := by
    rw [matrix_log, Matrix.IsHermitian.cfc_eq ρ.toIsHermitian Real.log]
    rfl
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
      _ = Matrix.trace (D * L) := canonical_trace_unitary_conj U (D * L)
  have hsum : (Matrix.trace (ρ.matrix * matrix_log ρ.matrix)).re =
      ∑ i : Fin n, ρ.eigenvalues i * Real.log (ρ.eigenvalues i) := by
    rw [htrace, hDdef, hLdef, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp
  rw [hsum, von_neumann_entropy, neg_neg]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : ρ.eigenvalues i = 0
  · simp [hi]
  · simp [hi]

/-- The canonical state's own entropy/energy relation, from the crux lemma applied to `ρ = canonical_state H β`
    itself: `S(γ) = β·E(γ) + log Z`. -/
private lemma canonical_entropy_eq {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) :
    von_neumann_entropy (canonical_state H β) =
      β * ((canonical_state H β).matrix * H.matrix).trace.re +
        Real.log (∑ j : Fin n, Real.exp (-β * H.toIsHermitian.eigenvalues j)) := by
  set Z := ∑ j : Fin n, Real.exp (-β * H.toIsHermitian.eigenvalues j) with hZdef
  have hentropy := trace_self_log_eq_neg_entropy (canonical_state H β)
  have hcrux : matrix_log (canonical_state H β).matrix = -(β : ℂ) • H.matrix - (Real.log Z : ℂ) • 1 :=
    canonical_matrix_log H β
  have htrace1 : (canonical_state H β).matrix.trace = 1 := (canonical_state H β).normalized
  have hexpand :
      Matrix.trace ((canonical_state H β).matrix * matrix_log (canonical_state H β).matrix) =
        -(β : ℂ) * Matrix.trace ((canonical_state H β).matrix * H.matrix) -
          (Real.log Z : ℂ) * Matrix.trace (canonical_state H β).matrix := by
    rw [hcrux, mul_sub, Matrix.trace_sub, mul_smul_comm, mul_smul_comm, Matrix.mul_one,
      Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  rw [htrace1, mul_one] at hexpand
  have hre := congrArg Complex.re hexpand
  rw [hentropy] at hre
  simp only [Complex.sub_re, neg_mul, Complex.neg_re, Complex.re_ofReal_mul,
    Complex.ofReal_re] at hre
  linarith [hre]

-- REMOVED 2026-07-02 (self-improvement loop, boundary_violation): the axiom
-- `max_entropy_at_fixed_energy` was FALSE as stated — its `∃ β > 0` with canonical energy = E fails
-- for E outside the achievable open interval (qubit H {0,1}: energy ∈ (0,1/2) for β∈(0,∞), so E=0.9
-- has no witness). It had no consumers, so it is deleted. The true Jaynes max-entropy principle
-- (canonical_state at a GIVEN β maximises entropy among equal-energy states) is a future loop target.

/-- Relative coherence `C_rel(ρ) = D(ρ || Δρ)` for fixed-basis dephasing. -/
noncomputable def relative_coherence {n : ℕ} (ρ : DensityMatrix n) : ℝ :=
  relative_entropy_real ρ (pinching ρ)

/-- Coherent free-energy surplus. -/
theorem coherent_free_energy_surplus {n : ℕ}
    (ρ : DensityMatrix n) (H : Hermitian n) (β : ℝ)
    (h_β : β > 0)
    (h_energy_basis :
      ((ρ.matrix * H.matrix).trace.re) =
        (((pinching ρ).matrix * H.matrix).trace.re))
    (h_coherence_def :
      relative_coherence ρ =
        von_neumann_entropy (pinching ρ) - von_neumann_entropy ρ) :
  free_energy ρ H β - free_energy (pinching ρ) H β =
    (1 / β) * relative_coherence ρ := by
  have _ : β > 0 := h_β
  unfold free_energy
  rw [h_energy_basis, h_coherence_def]
  ring

/-- Coherence is nonnegative under the finite relative-entropy support condition. -/
theorem coherence_nonneg {n : ℕ} (ρ : DensityMatrix n) (h : support_le ρ (pinching ρ)) :
  0 ≤ relative_coherence ρ :=
  relative_entropy_real_nonneg_of_support ρ (pinching ρ) h

theorem coherence_zero_iff_diagonal {n : ℕ} (ρ : DensityMatrix n)
    (h : support_le ρ (pinching ρ)) :
  relative_coherence ρ = 0 ↔ ρ = pinching ρ :=
  relative_entropy_eq_zero_iff ρ (pinching ρ) h

theorem coherence_bound {n : ℕ} (ρ : DensityMatrix n) :
  relative_coherence ρ ≤ Real.log (n : ℝ) := by
  rw [relative_coherence, relative_entropy_pinching_eq_entropy_diff ρ]
  have hmax : von_neumann_entropy (pinching ρ) ≤ Real.log (n : ℝ) :=
    entropy_max_at_mixed (pinching ρ)
  have hnonneg : 0 ≤ von_neumann_entropy ρ := entropy_nonneg ρ
  linarith

theorem canonical_coherence_bound {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) :
  relative_coherence (canonical_state H β) ≤ Real.log (n : ℝ) := by
  exact coherence_bound (canonical_state H β)

theorem coherence_monotone_incoherent {n : ℕ} (ρ : DensityMatrix n)
    (Φ : CPTPMap n) (h_incoherent :
      ∀ σ : DensityMatrix n,
        (∀ i j, i ≠ j → σ.matrix i j = 0) →
          ∀ i j, i ≠ j → (Φ.apply σ).matrix i j = 0) :
  relative_coherence (Φ.apply ρ) ≤ relative_coherence ρ := by
  unfold relative_coherence
  have hdpi :
      relative_entropy_real (Φ.apply ρ) (Φ.apply (pinching ρ)) ≤
        relative_entropy_real ρ (pinching ρ) :=
    relative_entropy_monotone Φ ρ (pinching ρ) (support_le_pinching ρ)
  have hpin_diag :
      ∀ i j, i ≠ j → (pinching ρ).matrix i j = 0 := by
    intro i j hij
    show Matrix.diagonal (fun k : Fin n => ρ.matrix k k) i j = 0
    exact Matrix.diagonal_apply_ne _ hij
  have hΦpin_diag :
      ∀ i j, i ≠ j → (Φ.apply (pinching ρ)).matrix i j = 0 :=
    h_incoherent (pinching ρ) hpin_diag
  have hsupport :
      support_le (Φ.apply ρ) (Φ.apply (pinching ρ)) :=
    support_le_cptp Φ (support_le_pinching ρ)
  have hmin :
      relative_entropy_real (Φ.apply ρ) (pinching (Φ.apply ρ)) ≤
        relative_entropy_real (Φ.apply ρ) (Φ.apply (pinching ρ)) :=
    relative_entropy_pinching_le_of_diagonal
      (Φ.apply ρ) (Φ.apply (pinching ρ)) hΦpin_diag hsupport
  exact hmin.trans hdpi

/-! ### Non-vacuity witnesses for `coherence_monotone_incoherent` (soundness audit 2026-07-02)

Two junk-safety observations back the axiom (see SOUNDNESS_AUDIT.md):
(1) `support_le ρ (pinching ρ)` holds for EVERY ρ (`support_le_pinching`), so BOTH sides of
    the statement are always honest relative-entropy values — the `Real.log 0 = 0` junk
    convention cannot produce a false instance here (unlike the refuted unconditional
    joint-convexity statement).
(2) The hypothesis class is non-empty and the conclusion is machine-checkable on a concrete,
    non-trivial member: the dephasing channel. -/

/-- The dephasing channel satisfies the axiom's incoherence hypothesis (its output is ALWAYS
    diagonal), so the hypothesis is not a dead quantifier. -/
theorem dephasing_channel_incoherent {n : ℕ} :
    ∀ σ : DensityMatrix n, (∀ i j, i ≠ j → σ.matrix i j = 0) →
      ∀ i j, i ≠ j → ((dephasing_channel n).apply σ).matrix i j = 0 := by
  intro σ _ i j hij
  rw [dephasing_channel_apply_matrix]
  show Matrix.diagonal _ i j = 0
  exact Matrix.diagonal_apply_ne _ hij

/-- WITNESS: the axiom's conclusion holds for the dephasing channel at EVERY state — proven
    without the axiom (dephasing kills all coherence; Klein's inequality bounds the right side
    from below by 0). -/
theorem coherence_monotone_dephasing_instance {n : ℕ} (ρ : DensityMatrix n) :
    relative_coherence ((dephasing_channel n).apply ρ) ≤ relative_coherence ρ := by
  have h0 : relative_coherence ((dephasing_channel n).apply ρ) = 0 := by
    unfold relative_coherence
    apply relative_entropy_real_eq_zero_of_matrix_eq
    calc ((dephasing_channel n).apply ρ).matrix
        = (pinching ρ).matrix := dephasing_channel_apply_matrix ρ
      _ = (pinching (pinching ρ)).matrix := (pinching_pinching_matrix ρ).symm
      _ = (pinching ((dephasing_channel n).apply ρ)).matrix :=
          (pinching_matrix_congr (dephasing_channel_apply_matrix ρ)).symm
  rw [h0]
  exact coherence_nonneg ρ (support_le_pinching ρ)

#print axioms dephasing_channel_incoherent
#print axioms coherence_monotone_dephasing_instance

/-- `partition_function` (defined via `NormedSpace.exp`) agrees with the eigen-sum `Z` — via the
    matrix-native `Matrix.exp_diagonal`/`Matrix.exp_conj` (which hide the "no canonical matrix
    norm" issue internally, needing only a norm on the *entries* `ℂ`), applied in `H`'s own
    eigenbasis, avoiding any need for a `NormedRing (Matrix n n ℂ)` instance. -/
private lemma partition_function_eq_sum_exp {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) :
    partition_function H β =
      ∑ j : Fin n, Real.exp (-β * H.toIsHermitian.eigenvalues j) := by
  set V := H.toIsHermitian.eigenvectorUnitary
  have hV1 : (V : Matrix (Fin n) (Fin n) ℂ) * star (V : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    (Matrix.mem_unitaryGroup_iff).mp V.2
  have hVinv : (V : Matrix (Fin n) (Fin n) ℂ)⁻¹ = star (V : Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.inv_eq_right_inv hV1
  have hVunit : IsUnit (V : Matrix (Fin n) (Fin n) ℂ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.UnitaryGroup.det_isUnit V)
  have hH : H.matrix = (V : Matrix (Fin n) (Fin n) ℂ) *
      Matrix.diagonal (fun i : Fin n => (H.toIsHermitian.eigenvalues i : ℂ)) *
      star (V : Matrix (Fin n) (Fin n) ℂ) := by
    simpa [V] using hermitian_spectral_cfe H
  have hscale : -(β : ℂ) • H.matrix = (V : Matrix (Fin n) (Fin n) ℂ) *
      Matrix.diagonal (fun i : Fin n => -(β : ℂ) * H.toIsHermitian.eigenvalues i) *
      star (V : Matrix (Fin n) (Fin n) ℂ) := by
    conv_lhs => rw [hH]
    rw [← smul_mul_assoc, ← mul_smul_comm, ← Matrix.diagonal_smul]
    congr 2
  have hexp : NormedSpace.exp (-(β : ℂ) • H.matrix) =
      (V : Matrix (Fin n) (Fin n) ℂ) *
        NormedSpace.exp (Matrix.diagonal
          (fun i : Fin n => -(β : ℂ) * H.toIsHermitian.eigenvalues i)) *
        star (V : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hscale, ← hVinv]
    exact Matrix.exp_conj _ _ hVunit
  rw [partition_function, hexp, Matrix.exp_diagonal, canonical_trace_unitary_conj,
    Matrix.trace_diagonal]
  simp only [Pi.exp_def, ← Complex.exp_eq_exp_ℂ]
  rw [Complex.re_sum]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.exp_ofReal_re]

/-- Discharged (was an axiom): the canonical free energy in terms of the partition function. -/
theorem canonical_free_energy_from_partition {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ)
    (h_β : β > 0) :
  free_energy (canonical_state H β) H β =
    - (1 / β) * Real.log (partition_function H β) := by
  rw [partition_function_eq_sum_exp, free_energy, canonical_entropy_eq]
  have hZpos := canonical_partition_pos H β
  field_simp
  ring

/-- Gibbs identity relating relative entropy and the free-energy gap, for `β > 0`.
    RESTATED 2026-07-02 (self-improvement loop): the previous unguarded form was FALSE at β=0 (the
    `1/β` in `free_energy`). Adding `(h_β : β > 0)` removes that false case; with β>0 it is true and
    reachable from the in-file `canonical_matrix_log` crux. Discharged (was an axiom) via the
    `canonical_matrix_log`/`trace_self_log_eq_neg_entropy`/`canonical_free_energy_from_partition`
    trio. -/
theorem relative_entropy_gibbs_identity {n : ℕ} [NeZero n]
    (ρ : DensityMatrix n) (H : Hermitian n) (β : ℝ) (h_β : β > 0) :
  relative_entropy_real ρ (canonical_state H β) =
    β * (free_energy ρ H β - free_energy (canonical_state H β) H β) := by
  set Z := ∑ j : Fin n, Real.exp (-β * H.toIsHermitian.eigenvalues j) with hZdef
  have hcrux : matrix_log (canonical_state H β).matrix =
      -(β : ℂ) • H.matrix - (Real.log Z : ℂ) • 1 :=
    canonical_matrix_log H β
  have hself : (Matrix.trace (ρ.matrix * matrix_log ρ.matrix)).re = -von_neumann_entropy ρ :=
    trace_self_log_eq_neg_entropy ρ
  have htrace1 : ρ.matrix.trace = 1 := ρ.normalized
  have hexpand :
      Matrix.trace (ρ.matrix * matrix_log (canonical_state H β).matrix) =
        -(β : ℂ) * Matrix.trace (ρ.matrix * H.matrix) -
          (Real.log Z : ℂ) * Matrix.trace ρ.matrix := by
    rw [hcrux, mul_sub, Matrix.trace_sub, mul_smul_comm, mul_smul_comm, Matrix.mul_one,
      Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  rw [htrace1, mul_one] at hexpand
  have hre := congrArg Complex.re hexpand
  simp only [Complex.sub_re, neg_mul, Complex.neg_re, Complex.re_ofReal_mul,
    Complex.ofReal_re] at hre
  have hFγ : free_energy (canonical_state H β) H β = -(1 / β) * Real.log Z := by
    have h := canonical_free_energy_from_partition H β h_β
    rwa [partition_function_eq_sum_exp] at h
  unfold relative_entropy_real
  rw [mul_sub, Matrix.trace_sub, Complex.sub_re, hself, hre, hFγ]
  unfold free_energy
  have hβne : β ≠ 0 := h_β.ne'
  field_simp
  ring

/-- Gibbs variational principle. -/
theorem canonical_minimizes_free_energy {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ)
    (h_β : β > 0) :
  ∀ ρ : DensityMatrix n,
    free_energy (canonical_state H β) H β ≤ free_energy ρ H β := by
  intro ρ
  have h_rel := relative_entropy_gibbs_identity ρ H β h_β
  have h_nonneg := relative_entropy_real_nonneg_of_support ρ (canonical_state H β)
    (support_le_canonical ρ H β)
  nlinarith

noncomputable def canonical_energy {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) : ℝ :=
  ((canonical_state H β).matrix * H.matrix).trace.re

noncomputable def canonical_entropy {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) : ℝ :=
  von_neumann_entropy (canonical_state H β)

theorem thermodynamic_identity {n : ℕ} [NeZero n] (H : Hermitian n) (β : ℝ) :
    free_energy (canonical_state H β) H β =
      canonical_energy H β - (1 / β) * canonical_entropy H β := by
  rfl

end Quantum
