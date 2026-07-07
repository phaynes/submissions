/-
  Proofs/Correspondence.lean
  Concrete (non-abstract) Stochastic-Quantum Correspondence interface.

  This module is the intended REPLACEMENT for the abstract surface in `Proofs/SQT_Axiom.lean`,
  whose `stochastic_quantum_theorem` is satisfiable by a trivial witness (its correspondence
  fields are `Nonempty (Struct …)` with no cross-side equations). Here the interface fields ARE
  the cross-side equations, the dynamics-matching field is shown to have teeth (it forces
  column-stochasticity), and the interface is inhabited by a fully machine-checked instance.

  It lives in its own namespace `Quantum.SQC` and is imported by `SQT_Axiom.lean`.
  The old abstract existential has been removed from the active axiom surface; the
  general Barandes reconstruction theorem remains future work.

  Acceptance: this module must keep `lake build` green and must satisfy
  `sqc-proof-gate --require-instance SQCorrespondence`.

  Keep imports narrow so this interface does not force a rebuild of all Mathlib.
-/
import Proofs.BasicDefinitions
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open scoped Matrix BigOperators
open Matrix

namespace Quantum.SQC

/-- Stochastic side: a finite distribution and a column-stochastic transition matrix.
    No Markov/semigroup law is assumed, so Barandes' indivisibility is preserved. -/
structure StochasticDynamics (n : ℕ) where
  p0        : Fin n → ℝ
  p0_nonneg : ∀ i, 0 ≤ p0 i
  p0_sum    : ∑ i, p0 i = 1
  Γ         : Matrix (Fin n) (Fin n) ℝ
  Γ_nonneg  : ∀ i j, 0 ≤ Γ i j
  Γ_stoch   : ∀ j, ∑ i, Γ i j = 1

/-- The correspondence interface. The non-trivial field `dyn_match` is the unistochastic
    matching `Γᵢⱼ = |Uᵢⱼ|²` — the content the abstract `Nonempty (DynamicsCorrespondence …)`
    placeholder lacked. -/
structure SQCorrespondence (n : ℕ) (D : StochasticDynamics n) where
  U         : Matrix (Fin n) (Fin n) ℂ
  U_unitary : U.conjTranspose * U = 1
  dyn_match : ∀ i j, D.Γ i j = Complex.normSq (U i j)

/-- **The interface has teeth.** From `U` unitary and `Γ = |U|²`, column-stochasticity of `Γ`
    is *forced*: it is a theorem, not an independent assumption. (Upstream this is the axiom
    `unitary_channel_bistochastic`; here it is discharged.) -/
theorem corr_consistency {n : ℕ} {D : StochasticDynamics n}
    (C : SQCorrespondence n D) (j : Fin n) :
    ∑ i, D.Γ i j = 1 := by
  have hterm : ∀ i, (star (C.U i j)) * (C.U i j) = ((Complex.normSq (C.U i j) : ℝ) : ℂ) := by
    intro i
    rw [mul_comm]
    simpa using Complex.mul_conj (C.U i j)
  have hjj : (C.U.conjTranspose * C.U) j j = ((∑ i, Complex.normSq (C.U i j) : ℝ) : ℂ) := by
    rw [Matrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Matrix.conjTranspose_apply]
    exact hterm i
  rw [C.U_unitary, Matrix.one_apply_eq] at hjj
  have hsum : (∑ i, Complex.normSq (C.U i j)) = 1 := by
    have := hjj.symm
    exact_mod_cast this
  calc ∑ i, D.Γ i j
      = ∑ i, Complex.normSq (C.U i j) := Finset.sum_congr rfl (fun i _ => C.dyn_match i j)
    _ = 1 := hsum

/-! ## A fully-discharged concrete instance: a deterministic 2-state swap (NOT gate).

    `U = !![0,1; 1,0]` is unitary; its unistochastic image is `Γ = !![0,1; 1,0]`. This is the
    machine-checked witness that satisfies the positive-instance obligation. -/

noncomputable def Uswap : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
noncomputable def Γswap : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
noncomputable def p0swap : Fin 2 → ℝ := ![1, 0]

noncomputable def dynSwap : StochasticDynamics 2 where
  p0 := p0swap
  p0_nonneg := by intro i; fin_cases i <;> simp [p0swap]
  p0_sum := by simp [p0swap, Fin.sum_univ_two]
  Γ := Γswap
  Γ_nonneg := by intro i j; fin_cases i <;> fin_cases j <;> simp [Γswap]
  Γ_stoch := by intro j; fin_cases j <;> simp [Γswap, Fin.sum_univ_two]

noncomputable def swap : SQCorrespondence 2 dynSwap where
  U := Uswap
  U_unitary := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Uswap, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  dyn_match := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [dynSwap, Γswap, Uswap]

/-- The instance's `Γ` is column-stochastic as a *consequence* of `corr_consistency`. -/
example (j : Fin 2) : ∑ i, dynSwap.Γ i j = 1 := corr_consistency swap j

/-! ## A refutable example: a column-stochastic Γ that is NOT unistochastic for `Uswap`. -/

noncomputable def badΓ : Matrix (Fin 2) (Fin 2) ℝ := !![(1/2 : ℝ), (1/2 : ℝ); (1/2 : ℝ), (1/2 : ℝ)]

theorem not_unistochastic_example :
    ¬ (∀ i j, badΓ i j = Complex.normSq (Uswap i j)) := by
  intro h
  have h00 := h 0 0
  rw [show badΓ 0 0 = (1/2 : ℝ) from rfl, show Uswap 0 0 = (0 : ℂ) from rfl,
      Complex.normSq_zero] at h00
  norm_num at h00

/-! ## Tier 1 instrument laws: diagonal probabilities and a non-permutation instance. -/

/-- Classical expectation on the stochastic side. -/
noncomputable def classicalExpectation {n : ℕ} (D : StochasticDynamics n) (f : Fin n → ℝ) : ℝ :=
  ∑ i, D.p0 i * f i

/-- Quantum expectation for the diagonal density `diag(p0)` and diagonal observable `diag(f)`. -/
noncomputable def diagonalQuantumExpectation {n : ℕ}
    (D : StochasticDynamics n) (f : Fin n → ℝ) : ℝ :=
  (((Matrix.diagonal fun i : Fin n => (D.p0 i : ℂ)) *
      (Matrix.diagonal fun i : Fin n => (f i : ℂ))).trace).re

/-- The diagonal quantum observable agrees with the stochastic expectation. -/
theorem diagonal_observable_match {n : ℕ}
    (D : StochasticDynamics n) (f : Fin n → ℝ) :
    diagonalQuantumExpectation D f = classicalExpectation D f := by
  simp [diagonalQuantumExpectation, classicalExpectation, Matrix.trace, Matrix.mul_apply,
    Matrix.diagonal]

/-- One stochastic step using the transition matrix. -/
noncomputable def stochasticStep {n : ℕ} (D : StochasticDynamics n) (i : Fin n) : ℝ :=
  ∑ j, D.Γ i j * D.p0 j

/-- The diagonal of the unitary evolution induced by the correspondence. -/
noncomputable def quantumStepDiagonal {n : ℕ} {D : StochasticDynamics n}
    (C : SQCorrespondence n D) (i : Fin n) : ℝ :=
  ∑ j, Complex.normSq (C.U i j) * D.p0 j

/-- The unistochastic dynamics field gives the diagonal evolution law. -/
theorem diagonal_evolution_match {n : ℕ} {D : StochasticDynamics n}
    (C : SQCorrespondence n D) (i : Fin n) :
    stochasticStep D i = quantumStepDiagonal C i := by
  simp [stochasticStep, quantumStepDiagonal, C.dyn_match]

/-! A genuine superposition instance: the 3-4-5 real rotation.

    Unlike `swap`, this is not a permutation. Its stochastic image has nontrivial
    probabilities `9/25` and `16/25`, giving the gate two fully discharged
    positive instances to inspect. -/

noncomputable def U345 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![({ re := 3 / 5, im := 0 } : ℂ), ({ re := -(4 / 5), im := 0 } : ℂ);
     ({ re := 4 / 5, im := 0 } : ℂ), ({ re := 3 / 5, im := 0 } : ℂ)]

noncomputable def Γ345 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(9 / 25 : ℝ), (16 / 25 : ℝ); (16 / 25 : ℝ), (9 / 25 : ℝ)]

noncomputable def p0345 : Fin 2 → ℝ := ![(3 / 5 : ℝ), (2 / 5 : ℝ)]

noncomputable def dyn345 : StochasticDynamics 2 where
  p0 := p0345
  p0_nonneg := by intro i; fin_cases i <;> norm_num [p0345]
  p0_sum := by norm_num [p0345, Fin.sum_univ_two]
  Γ := Γ345
  Γ_nonneg := by intro i j; fin_cases i <;> fin_cases j <;> norm_num [Γ345]
  Γ_stoch := by intro j; fin_cases j <;> norm_num [Γ345, Fin.sum_univ_two]

noncomputable def rot345 : SQCorrespondence 2 dyn345 where
  U := U345
  U_unitary := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [U345, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        Complex.ext_iff]
  dyn_match := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [dyn345, Γ345, U345, Complex.normSq]

/-- The 3-4-5 rotation also has column-stochastic dynamics as a consequence. -/
example (j : Fin 2) : ∑ i, dyn345.Γ i j = 1 := corr_consistency rot345 j

end Quantum.SQC
