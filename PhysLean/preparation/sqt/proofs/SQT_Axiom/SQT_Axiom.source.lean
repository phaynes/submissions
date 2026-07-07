import Proofs.BasicDefinitions
import Proofs.PinchingEntropy
import Proofs.Correspondence

/-!
# Stochastic-Quantum Correspondence Axiom Surface

Restart-wave interface for the SQT/GKLS assumptions used by the proof
framework. The semigroup and entropy-production facts are explicit axioms.

The abstract `stochastic_quantum_theorem` existential has been retired from
this file. Concrete correspondence work now lives in `Proofs.Correspondence`
under `Quantum.SQC.SQCorrespondence`, where matching laws are data fields and
checked instances can be audited by `sqc-proof-gate`.
-/

namespace Quantum

open Matrix Real
open scoped BigOperators ComplexOrder

structure GKLSGenerator (n : ℕ) where
  hamiltonian : Hermitian n
  lindblad_ops : List (Matrix (Fin n) (Fin n) ℂ)

/-- Defined unitality predicate for the current finite-dimensional GKLS interface.

This is the standard Lindblad dissipator unitality condition in matrix form:
`∑ Lᵢ Lᵢ† = ∑ Lᵢ† Lᵢ`. It is a predicate over concrete generator data, not a
free proposition field stored inside the generator.
-/
noncomputable def IsUnitalGKLS {n : ℕ} (L : GKLSGenerator n) : Prop :=
  L.lindblad_ops.foldr
      (fun A acc => A * A.conjTranspose + acc)
      (0 : Matrix (Fin n) (Fin n) ℂ)
    =
    L.lindblad_ops.foldr
      (fun A acc => A.conjTranspose * A + acc)
      (0 : Matrix (Fin n) (Fin n) ℂ)

/-- NOTE (reclassified 2026-07-02): VACUOUS but SOUND, not false — this is a total function
    declaration `(generator, state, time) ↦ state` whose type is inhabited (e.g. the constant map),
    so it cannot prove `False` and is not a soundness defect to remove. It is, however, uninformative:
    it does not tie the output to the GKLS generator's dynamics, so `spohn_entropy_production` /
    `entropy_monotone_gkls` (the actual paper A3 assumptions) rest on an unconstrained evolution.
    Strengthening = give the generator a real defining law (semigroup / master-equation), after which
    those two should reduce to one lemma — future work, not a false-axiom removal. -/
axiom gkls_evolution {n : ℕ} :
  GKLSGenerator n → DensityMatrix n → ℝ → DensityMatrix n

noncomputable def entropy_production {n : ℕ} (ρ₀ ρ_t : DensityMatrix n) : ℝ :=
  von_neumann_entropy ρ_t - von_neumann_entropy ρ₀

axiom spohn_entropy_production {n : ℕ}
    (L : GKLSGenerator n) (ρ : DensityMatrix n) (t : ℝ)
    (h_unital : IsUnitalGKLS L) (h_pos : 0 < t) :
  entropy_production ρ (gkls_evolution L ρ t) ≥ 0

axiom entropy_monotone_gkls {n : ℕ}
    (L : GKLSGenerator n) (ρ : DensityMatrix n) (s t : ℝ)
    (h_unital : IsUnitalGKLS L) (h_order : 0 ≤ s ∧ s ≤ t) :
  von_neumann_entropy (gkls_evolution L ρ s) ≤
    von_neumann_entropy (gkls_evolution L ρ t)

/-! ## Satisfiability witnesses for the GKLS axiom surface (soundness audit 2026-07-02)

`gkls_evolution` is an OPAQUE axiom-declared function, and `spohn_entropy_production` /
`entropy_monotone_gkls` assert properties OF that opaque function. The soundness risk for such a
trio is joint UNSATISFIABILITY: if no function of that type could satisfy both properties, the
three axioms together would prove `False`. The witnesses below show the properties ARE jointly
satisfiable — the constant-in-time evolution `(L, ρ, t) ↦ ρ` inhabits the type and satisfies
both axiom statements verbatim. Hence the trio is a conservative (if dynamically uninformative)
extension: it cannot introduce an inconsistency. Kernel-checked; see `#print axioms` below. -/

/-- The constant-in-time evolution: a definable inhabitant of `gkls_evolution`'s type. -/
noncomputable def const_evolution {n : ℕ} :
    GKLSGenerator n → DensityMatrix n → ℝ → DensityMatrix n := fun _ ρ _ => ρ

/-- `spohn_entropy_production`'s statement holds for `const_evolution` (with `= 0`). -/
theorem const_evolution_spohn {n : ℕ}
    (L : GKLSGenerator n) (ρ : DensityMatrix n) (t : ℝ)
    (_h_unital : IsUnitalGKLS L) (_h_pos : 0 < t) :
    entropy_production ρ (const_evolution L ρ t) ≥ 0 := by
  simp [entropy_production, const_evolution]

/-- `entropy_monotone_gkls`'s statement holds for `const_evolution` (with `= `). -/
theorem const_evolution_entropy_monotone {n : ℕ}
    (L : GKLSGenerator n) (ρ : DensityMatrix n) (s t : ℝ)
    (_h_unital : IsUnitalGKLS L) (_h_order : 0 ≤ s ∧ s ≤ t) :
    von_neumann_entropy (const_evolution L ρ s) ≤
      von_neumann_entropy (const_evolution L ρ t) :=
  le_refl _

/-- Joint satisfiability of the GKLS axiom surface, packaged as one existential. -/
theorem gkls_axiom_surface_satisfiable (n : ℕ) :
    ∃ ev : GKLSGenerator n → DensityMatrix n → ℝ → DensityMatrix n,
      (∀ (L : GKLSGenerator n) (ρ : DensityMatrix n) (t : ℝ),
        IsUnitalGKLS L → 0 < t → entropy_production ρ (ev L ρ t) ≥ 0) ∧
      (∀ (L : GKLSGenerator n) (ρ : DensityMatrix n) (s t : ℝ),
        IsUnitalGKLS L → 0 ≤ s ∧ s ≤ t →
          von_neumann_entropy (ev L ρ s) ≤ von_neumann_entropy (ev L ρ t)) :=
  ⟨const_evolution,
    fun L ρ t hu hp => const_evolution_spohn L ρ t hu hp,
    fun L ρ s t hu ho => const_evolution_entropy_monotone L ρ s t hu ho⟩

#print axioms gkls_axiom_surface_satisfiable

/-- The `IsUnitalGKLS` hypothesis is not a dead quantifier: the generator with a single
    identity Lindblad operator satisfies it (so the two conditional axioms above are not
    vacuously scoped to an empty hypothesis class). -/
theorem isUnitalGKLS_witness {n : ℕ} :
    IsUnitalGKLS (⟨⟨0, by simp⟩, [1]⟩ : GKLSGenerator n) := by
  simp [IsUnitalGKLS]

#print axioms isUnitalGKLS_witness

structure WaveFunction (n : ℕ) where
  coefficients : Fin n → ℂ
  normalized : (Finset.univ.sum fun i : Fin n => Complex.normSq (coefficients i)) = 1

abbrev Hamiltonian (n : ℕ) := Hermitian n

theorem second_law_quantum {n : ℕ} (L : GKLSGenerator n) (ρ : DensityMatrix n)
    (h_unital : IsUnitalGKLS L) :
  ∀ t : ℝ, 0 < t →
    von_neumann_entropy ρ ≤ von_neumann_entropy (gkls_evolution L ρ t) := by
  intro t h_t
  have h := spohn_entropy_production L ρ t h_unital h_t
  simpa [entropy_production, ge_iff_le, sub_nonneg] using h

theorem entropy_production_nonneg {n : ℕ}
    (L : GKLSGenerator n) (ρ : DensityMatrix n) (t : ℝ)
    (h_unital : IsUnitalGKLS L) (h_t : 0 < t) :
  0 ≤ entropy_production ρ (gkls_evolution L ρ t) := by
  exact spohn_entropy_production L ρ t h_unital h_t

theorem entropy_rate_nonneg {n : ℕ}
    (L : GKLSGenerator n) (ρ : DensityMatrix n) (t : ℝ)
    (h_unital : IsUnitalGKLS L) (h_t : 0 < t) :
  von_neumann_entropy (gkls_evolution L ρ t) - von_neumann_entropy ρ ≥ 0 := by
  simpa [entropy_production] using spohn_entropy_production L ρ t h_unital h_t

end Quantum
