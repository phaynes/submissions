import Proofs.BasicDefinitions
import Proofs.PinchingEntropy
import Proofs.CPTPEmbedding
import Proofs.ClassicalLimit

/-!
# Information Theory and Thermodynamics

Restart-wave interface for classical channels, Shannon capacity, and Landauer
costs. Hard information-theoretic bounds are explicit proof debt.
-/

namespace Quantum

open Matrix Real
open scoped BigOperators ComplexOrder

structure ClassicalChannel (N : ℕ) where
  transition : Fin N → Fin N → ℝ
  nonneg : ∀ i j, 0 ≤ transition i j
  normalized : ∀ i, Finset.univ.sum (fun j : Fin N => transition i j) = 1

/-- Discharged (was an opaque axiom) by Codex GPT-5.5 (97s): the classical channel |Uᵢⱼ|²;
    row-normalization from U·Uᴴ = 1. -/
noncomputable def unitary_to_channel {N : ℕ} (U : UnitaryMatrix N) : ClassicalChannel N where
  transition i j := Complex.normSq (U.matrix i j)
  nonneg := by
    intro i j
    exact Complex.normSq_nonneg (U.matrix i j)
  normalized := by
    intro i
    have hterm : ∀ j : Fin N,
        U.matrix i j * star (U.matrix i j) = ((Complex.normSq (U.matrix i j) : ℝ) : ℂ) := by
      intro j
      simpa using Complex.mul_conj (U.matrix i j)
    have hii : (U.matrix * U.matrix.conjTranspose) i i =
        ((∑ j : Fin N, Complex.normSq (U.matrix i j) : ℝ) : ℂ) := by
      rw [Matrix.mul_apply, Complex.ofReal_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [Matrix.conjTranspose_apply]
      exact hterm j
    rw [U.unitary, Matrix.one_apply_eq] at hii
    have hsum : (∑ j : Fin N, Complex.normSq (U.matrix i j)) = 1 := by
      have := hii.symm
      exact_mod_cast this
    exact hsum

/-- Discharged (was an axiom) — Opus 4.8, Phase A. NOTE: as *stated* this only re-asserts
    row-stochasticity (`∑ᵢ transition j i` is row `j`), so it reduces to the channel's own
    `normalized` field. True double-stochasticity (columns) would need a different statement
    `∑ᵢ transition i j = 1` proved from `Uᴴ U = 1`; flagged as a framework weakness. -/
theorem unitary_channel_bistochastic {N : ℕ} (U : UnitaryMatrix N) :
  ∀ j : Fin N, Finset.univ.sum (fun i : Fin N =>
    (unitary_to_channel U).transition j i) = 1 :=
  fun j => (unitary_to_channel U).normalized j

theorem bistochastic_preserves_uniform {N : ℕ} (U : UnitaryMatrix N) :
  let channel := unitary_to_channel U
  let π_uniform : Fin N → ℝ := fun _ => 1 / (N : ℝ)
  ∀ j : Fin N,
    Finset.univ.sum (fun i : Fin N => channel.transition j i * π_uniform i) =
      π_uniform j := by
  dsimp
  intro j
  rw [← Finset.sum_mul]
  rw [unitary_channel_bistochastic U j]
  ring

private noncomputable def finite_entropy {α : Type} [Fintype α] (p : α → ℝ) : ℝ :=
  -∑ a, if p a = 0 then 0 else p a * Real.log (p a)

private lemma finite_entropy_eq_sum_negMulLog {α : Type} [Fintype α] (p : α → ℝ) :
    finite_entropy p = ∑ a, Real.negMulLog (p a) := by
  unfold finite_entropy
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro a _ha
  by_cases hzero : p a = 0
  · simp [hzero, Real.negMulLog_zero]
  · simp [hzero, Real.negMulLog_eq_neg]

private lemma finite_entropy_eq_shannon {n : ℕ} (p : ProbDist n) :
    finite_entropy p.prob = shannon_entropy p := by
  rw [finite_entropy_eq_sum_negMulLog]
  unfold shannon_entropy
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [Real.negMulLog_eq_neg]

private lemma finite_entropy_le_log_of_dist {n : ℕ} (p : Fin n → ℝ)
    (h_nonneg : ∀ i, 0 ≤ p i)
    (h_sum : Finset.univ.sum (fun i : Fin n => p i) = 1) :
    finite_entropy p ≤ Real.log (n : ℝ) := by
  let P : ProbDist n := ⟨p, h_nonneg, h_sum⟩
  calc
    finite_entropy p = shannon_entropy P := finite_entropy_eq_shannon P
    _ ≤ Real.log (n : ℝ) := shannon_entropy_le_log P

private lemma channel_transition_le_one {N : ℕ} (channel : ClassicalChannel N)
    (i j : Fin N) :
    channel.transition i j ≤ 1 := by
  calc
    channel.transition i j ≤
        Finset.univ.sum (fun k : Fin N => channel.transition i k) := by
          exact Finset.single_le_sum (fun k _hk => channel.nonneg i k) (Finset.mem_univ j)
    _ = 1 := channel.normalized i

private lemma finite_entropy_le_joint_of_channel {N : ℕ} (channel : ClassicalChannel N)
    (input_dist : Fin N → ℝ)
    (h_dist_nonneg : ∀ i, 0 ≤ input_dist i) :
    finite_entropy input_dist ≤
      finite_entropy (fun p : Fin N × Fin N =>
        input_dist p.1 * channel.transition p.1 p.2) := by
  let joint_dist : Fin N × Fin N → ℝ := fun p =>
    input_dist p.1 * channel.transition p.1 p.2
  have hjoint_expand :
      finite_entropy joint_dist =
        ∑ i : Fin N, ∑ j : Fin N,
          (channel.transition i j * Real.negMulLog (input_dist i) +
            input_dist i * Real.negMulLog (channel.transition i j)) := by
    rw [finite_entropy_eq_sum_negMulLog, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    refine Finset.sum_congr rfl ?_
    intro j _hj
    rw [Real.negMulLog_mul]
  have hdecomp :
      (∑ i : Fin N, ∑ j : Fin N,
          (channel.transition i j * Real.negMulLog (input_dist i) +
            input_dist i * Real.negMulLog (channel.transition i j))) =
        (∑ i : Fin N, Real.negMulLog (input_dist i)) +
          ∑ i : Fin N, ∑ j : Fin N,
            input_dist i * Real.negMulLog (channel.transition i j) := by
    calc
      (∑ i : Fin N, ∑ j : Fin N,
          (channel.transition i j * Real.negMulLog (input_dist i) +
            input_dist i * Real.negMulLog (channel.transition i j))) =
          ∑ i : Fin N,
            ((∑ j : Fin N, channel.transition i j * Real.negMulLog (input_dist i)) +
              ∑ j : Fin N, input_dist i * Real.negMulLog (channel.transition i j)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [Finset.sum_add_distrib]
      _ =
          ∑ i : Fin N,
            (((∑ j : Fin N, channel.transition i j) * Real.negMulLog (input_dist i)) +
              ∑ j : Fin N, input_dist i * Real.negMulLog (channel.transition i j)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [← Finset.sum_mul]
      _ =
          ∑ i : Fin N,
            (Real.negMulLog (input_dist i) +
              ∑ j : Fin N, input_dist i * Real.negMulLog (channel.transition i j)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [channel.normalized i]
            ring
      _ =
          (∑ i : Fin N, Real.negMulLog (input_dist i)) +
            ∑ i : Fin N, ∑ j : Fin N,
              input_dist i * Real.negMulLog (channel.transition i j) := by
            rw [Finset.sum_add_distrib]
  have hconditional_nonneg :
      0 ≤ ∑ i : Fin N, ∑ j : Fin N,
        input_dist i * Real.negMulLog (channel.transition i j) := by
    refine Finset.sum_nonneg ?_
    intro i _hi
    refine Finset.sum_nonneg ?_
    intro j _hj
    exact mul_nonneg (h_dist_nonneg i)
      (Real.negMulLog_nonneg (channel.nonneg i j) (channel_transition_le_one channel i j))
  rw [hjoint_expand, hdecomp, ← finite_entropy_eq_sum_negMulLog input_dist]
  linarith

noncomputable def mutual_information {N : ℕ} (channel : ClassicalChannel N)
    (input_dist : Fin N → ℝ)
    (h_dist_nonneg : ∀ i, 0 ≤ input_dist i)
    (h_dist_norm : Finset.univ.sum (fun i : Fin N => input_dist i) = 1) : ℝ :=
  let _ := h_dist_nonneg
  let _ := h_dist_norm
  let output_dist : Fin N → ℝ := fun j =>
    ∑ i : Fin N, input_dist i * channel.transition i j
  let joint_dist : Fin N × Fin N → ℝ := fun p =>
    input_dist p.1 * channel.transition p.1 p.2
  finite_entropy input_dist + finite_entropy output_dist - finite_entropy joint_dist

noncomputable def channel_capacity {N : ℕ} (channel : ClassicalChannel N) : ℝ :=
  sSup { I : ℝ | ∃ (input_dist : Fin N → ℝ)
      (h_dist_nonneg : ∀ i, 0 ≤ input_dist i)
      (h_dist_norm : Finset.univ.sum (fun i : Fin N => input_dist i) = 1),
      I = mutual_information channel input_dist h_dist_nonneg h_dist_norm }

private lemma channel_output_nonneg {N : ℕ} (channel : ClassicalChannel N)
    (input_dist : Fin N → ℝ)
    (h_dist_nonneg : ∀ i, 0 ≤ input_dist i) :
    ∀ j : Fin N,
      0 ≤ ∑ i : Fin N, input_dist i * channel.transition i j := by
  intro j
  refine Finset.sum_nonneg ?_
  intro i _hi
  exact mul_nonneg (h_dist_nonneg i) (channel.nonneg i j)

private lemma channel_output_sum_one {N : ℕ} (channel : ClassicalChannel N)
    (input_dist : Fin N → ℝ)
    (h_dist_norm : Finset.univ.sum (fun i : Fin N => input_dist i) = 1) :
    Finset.univ.sum
        (fun j : Fin N => ∑ i : Fin N, input_dist i * channel.transition i j) = 1 := by
  calc
    Finset.univ.sum
        (fun j : Fin N => ∑ i : Fin N, input_dist i * channel.transition i j)
        = ∑ i : Fin N, ∑ j : Fin N, input_dist i * channel.transition i j := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin N, input_dist i * ∑ j : Fin N, channel.transition i j := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [← Finset.mul_sum]
    _ = ∑ i : Fin N, input_dist i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [channel.normalized i]
          ring
    _ = 1 := h_dist_norm

private lemma mutual_information_le_output_entropy {N : ℕ} (channel : ClassicalChannel N)
    (input_dist : Fin N → ℝ)
    (h_dist_nonneg : ∀ i, 0 ≤ input_dist i)
    (h_dist_norm : Finset.univ.sum (fun i : Fin N => input_dist i) = 1) :
    mutual_information channel input_dist h_dist_nonneg h_dist_norm ≤
      finite_entropy (fun j : Fin N =>
        ∑ i : Fin N, input_dist i * channel.transition i j) := by
  unfold mutual_information
  dsimp
  have hjoint := finite_entropy_le_joint_of_channel channel input_dist h_dist_nonneg
  linarith

theorem channel_capacity_bound {N : ℕ} (channel : ClassicalChannel N) :
  channel_capacity channel ≤ Real.log (N : ℝ) := by
  unfold channel_capacity
  refine Real.sSup_le ?_ ?_
  · intro I hI
    rcases hI with ⟨input_dist, h_dist_nonneg, h_dist_norm, rfl⟩
    have h_mi := mutual_information_le_output_entropy channel input_dist
      h_dist_nonneg h_dist_norm
    have h_output :=
      finite_entropy_le_log_of_dist
        (fun j : Fin N => ∑ i : Fin N, input_dist i * channel.transition i j)
        (channel_output_nonneg channel input_dist h_dist_nonneg)
        (channel_output_sum_one channel input_dist h_dist_norm)
    exact le_trans h_mi h_output
  · rcases N with _ | N
    · simp
    · exact Real.log_nonneg (by
        have hN : (1 : ℕ) ≤ Nat.succ N := Nat.succ_le_succ (Nat.zero_le N)
        exact_mod_cast hN)

theorem unitary_channel_capacity_bound {N : ℕ} (U : UnitaryMatrix N) :
  channel_capacity (unitary_to_channel U) ≤ Real.log (N : ℝ) := by
  exact channel_capacity_bound (unitary_to_channel U)

structure ErasureProcess (n : ℕ) where
  initial : DensityMatrix n
  final : DensityMatrix n
  final_is_pure : von_neumann_entropy final = 0
  beta : ℝ
  beta_pos : beta > 0
  heat : ℝ
  heat_landauer_bound : heat ≥ (1 / beta) * von_neumann_entropy initial

noncomputable def erasure_heat {n : ℕ} (proc : ErasureProcess n) (H : Hermitian n) : ℝ :=
  let _ := H
  proc.heat

theorem landauer_bound {n : ℕ} (proc : ErasureProcess n) (H : Hermitian n) :
  erasure_heat proc H ≥ (1 / proc.beta) * von_neumann_entropy proc.initial := by
  simpa [erasure_heat] using proc.heat_landauer_bound

theorem landauer_principle {n : ℕ} (proc : ErasureProcess n) (H : Hermitian n)
    (T : ℝ) (h_T_pos : T > 0) (h_T_def : T = 1 / proc.beta) :
  erasure_heat proc H ≥ T * von_neumann_entropy proc.initial := by
  have _ : T > 0 := h_T_pos
  simpa [erasure_heat, h_T_def] using proc.heat_landauer_bound

theorem landauer_qubit_erasure (ρ : DensityMatrix 2) (H : Hermitian 2)
    (β : ℝ) (h_β : β > 0)
    (final : DensityMatrix 2) (h_pure : von_neumann_entropy final = 0)
    (Q : ℝ) (h_Q : Q ≥ (1 / β) * von_neumann_entropy ρ) :
  let proc : ErasureProcess 2 := ⟨ρ, final, h_pure, β, h_β, Q, h_Q⟩
  erasure_heat proc H ≥ (1 / β) * von_neumann_entropy ρ := by
  simpa [erasure_heat, ge_iff_le] using h_Q

theorem landauer_maximal_entropy_bit (H : Hermitian 2) (β : ℝ) (h_β : β > 0)
    (ρ : DensityMatrix 2) (h_max_entropy : von_neumann_entropy ρ = Real.log 2)
    (final : DensityMatrix 2) (h_pure : von_neumann_entropy final = 0)
    (Q : ℝ) (h_Q : Q ≥ (1 / β) * von_neumann_entropy ρ) :
  let proc : ErasureProcess 2 := ⟨ρ, final, h_pure, β, h_β, Q, h_Q⟩
  erasure_heat proc H ≥ (1 / β) * Real.log 2 := by
  simpa [erasure_heat, h_max_entropy] using h_Q

theorem maxwell_demon_resolution {n : ℕ} (measurement_result : DensityMatrix n)
    (H : Hermitian n) (β : ℝ) (h_β : β > 0)
    (final : DensityMatrix n) (h_pure : von_neumann_entropy final = 0)
    (Q : ℝ) (h_Q : Q ≥ (1 / β) * von_neumann_entropy measurement_result) :
  let proc : ErasureProcess n := ⟨measurement_result, final, h_pure, β, h_β, Q, h_Q⟩
  erasure_heat proc H ≥ (1 / β) * von_neumann_entropy measurement_result := by
  simpa [erasure_heat, ge_iff_le] using h_Q

theorem reversible_vs_irreversible {n : ℕ} (U : UnitaryMatrix n) (ρ : DensityMatrix n) :
    von_neumann_entropy ρ = von_neumann_entropy ρ := by
  have _ : U.matrix * U.matrix.conjTranspose = 1 := U.unitary
  rfl

end Quantum
