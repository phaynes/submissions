# Fable review — `Proofs/CoherentFreeEnergy.lean`

**Module:** `verification/lean/Proofs/CoherentFreeEnergy.lean` (489 lines, 0 declared axioms)
**Reviewer:** Fable 5 (analysis only; no source edits)
**Date:** 2026-07-08
**Method:** full read of the module; read of all upstream definitions it consumes
(`pinching`, `support_le`, `relative_entropy_real`, `von_neumann_entropy`, `matrix_log`,
the DPI/Klein/pinching lemmas in `PinchingEntropy.lean`, `dephasing_channel`); plus a
kernel check (`lake env lean` + `#print axioms`) on all 12 public theorems of this module.

---

## 1. What this module proves

The thermodynamic layer of the development, in two halves:

**Canonical-state half (the real work).**
- `free_energy` (line 21): `F(ρ) = Re Tr(ρH) − (1/β)·S(ρ)`.
- `partition_function` (line 27): `Z = Re Tr(exp(−βH))`, proved equal to the eigen-sum
  `Σᵢ exp(−βμᵢ)` in `partition_function_eq_sum_exp` (line 387) via `Matrix.exp_conj` /
  `Matrix.exp_diagonal` in `H`'s own eigenbasis — so the definition is not a stub and the
  `.re` hides nothing.
- `canonical_state` (line 142): the Gibbs state built **spectrally** — `V·diag(wᵢ)·V†` with
  `wᵢ = exp(−βμᵢ)/Z` — with positive-definiteness (`canonical_matrix_posDef`, line 115) and
  trace 1 (`canonical_matrix_trace`, line 131) proved, not assumed.
- `canonical_matrix_log` (line 178, correctly labeled "crux lemma"): `log γ_β = −βH − (log Z)·1`
  via the composition property of the continuous functional calculus. Everything downstream
  hangs off this.
- `relative_entropy_gibbs_identity` (line 436): `D(ρ‖γ_β) = β(F(ρ) − F(γ_β))` for `β > 0` —
  the identity that was formerly a (once misstated, then restated-with-guard) axiom, now a
  theorem.
- `canonical_minimizes_free_energy` (line 468): the Gibbs variational principle, from the
  identity plus Klein nonnegativity (γ_β is PosDef, so `support_le ρ γ_β` holds for every ρ —
  `support_le_canonical`, line 155).

**Coherence half (leaf results; nothing downstream consumes them).**
- `relative_coherence` (line 273): `C(ρ) = D(ρ‖Δρ)` for fixed-basis dephasing `Δ = pinching`.
- Nonnegativity, `= 0 ↔ diagonal`, `≤ log n` bounds (lines 294–313).
- `coherence_monotone_incoherent` (line 315): coherence monotonicity under channels that
  preserve diagonal states (the MIO class), proved by the textbook route: pinching-minimality
  among diagonal references (`relative_entropy_pinching_le_of_diagonal`) chained with the
  data-processing inequality (`relative_entropy_monotone`, itself discharged through the
  physlib DPI, not through the joint-convexity axiom).
- Non-vacuity witnesses (lines 356–378): the dephasing channel satisfies the hypothesis class
  and the conclusion, checked end-to-end.

In the DAG this module sits between `PinchingEntropy` (entropy core) and `MaxEntCanonical`
(which consumes `canonical_state` and `relative_entropy_gibbs_identity`).

## 2. Soundness review

**Headline (kernel-verified): this module is unconditional — stronger than "0 declared
axioms."** I ran `#print axioms` on all 12 public theorems (`canonical_state_posDef`,
`support_le_canonical`, `coherent_free_energy_surplus`, `coherence_nonneg`,
`coherence_zero_iff_diagonal`, `coherence_bound`, `canonical_coherence_bound`,
`coherence_monotone_incoherent`, `canonical_free_energy_from_partition`,
`relative_entropy_gibbs_identity`, `canonical_minimizes_free_energy`,
`thermodynamic_identity`). Every one depends only on `[propext, Classical.choice,
Quot.sound]`. None inherits `relative_entropy_jointly_convex` (the one `PinchingEntropy`
axiom) or any `SQT_Axiom` assumption — the DPI used by `coherence_monotone_incoherent`
routes through the physlib proof, not the axiom. The project docs (PROOF_STATUS,
axiom-surface) only state the weaker per-module "0 axioms" fact; the transitive cleanliness
is worth recording (see §5).

**Junk-value audit (the module-specific focus) — clean.** I checked every definition against
the known junk conventions (`Real.log 0 = 0`, `1/0 = 0`):

- `relative_coherence` can never hit the junk regime of `relative_entropy_real`: the support
  condition `support_le ρ (pinching ρ)` holds for **every** ρ (`support_le_pinching`,
  PinchingEntropy:292), so `D(ρ‖Δρ)` is always the honest quantity. The comment block at
  lines 344–352 makes exactly this argument and it checks out.
- `canonical_state` is a genuine spectral construction (PosDef, trace-1 proved), valid for
  all real β (β = 0 gives the maximally mixed state; negative β is a legitimate
  negative-temperature Gibbs state for a bounded H). No stub.
- `partition_function` is proved equal to the positive eigen-sum (line 387), so `log Z` in
  the crux lemma is applied to a strictly positive real (`canonical_partition_pos`, line 71).
- `matrix_log` on `canonical_matrix` acts on a PosDef matrix — `Real.log` never sees 0 there.
  In `trace_self_log_eq_neg_entropy` (line 203) it *can* see zero eigenvalues of ρ, and the
  final `by_cases hi : ρ.eigenvalues i = 0` (lines 238–240) reconciles the junk `0·log 0 = 0`
  with the `if λ = 0 then 0` guard inside `von_neumann_entropy` (PhyslibBridge:21) — both
  sides use the same convention, so the lemma is honestly true.
- `free_energy`'s only junk point is `1/β` at β = 0; every theorem where that would be
  load-bearing (`canonical_free_energy_from_partition`, `relative_entropy_gibbs_identity`,
  `canonical_minimizes_free_energy`) guards `β > 0`. The 2026-07-02 restatement note at
  lines 430–435 is accurate: the unguarded Gibbs identity is false at β = 0, and the guard
  is real.

**Finding S1 — `coherent_free_energy_surplus` (line 277) is materially weaker than its name:
its physics content is entirely in its hypotheses.** The proof body is `rw [...]; ring`.
Specifically:

- `h_coherence_def` assumes `C(ρ) = S(Δρ) − S(ρ)` — but this exact statement is a **proved,
  unconditional theorem**, `relative_entropy_pinching_eq_entropy_diff`
  (PinchingEntropy:550), which this very module uses three lines later in `coherence_bound`
  (line 305). The hypothesis is redundant and should be discharged; as stated, the module's
  marquee-named theorem *assumes* the identity the framework proved.
- `h_β : β > 0` is dead: line 288 binds it to `_` (`have _ : β > 0 := h_β`) and the `ring`
  step holds for all β (at β = 0 both sides collapse to 0 under `1/0 = 0`). A reader will
  assume the guard is load-bearing; it is not. Either drop it or comment it as a
  physical-domain restriction only.
- `h_energy_basis` (`Tr(ρH) = Tr(Δρ·H)`) is the one *genuine* restriction — it encodes "H is
  incoherent in the dephasing basis" (true e.g. for diagonal H, false in general). It is
  honestly stated, but nothing tells the reader when it is satisfiable; a companion lemma
  "H diagonal → `h_energy_basis`" would make the hypothesis class visibly non-empty, in the
  same spirit as the existing dephasing witnesses.

Not unsound — nothing false is claimed — but this is exactly the "theorem weaker than it
looks" pattern the review brief asks about. No downstream module consumes it, so
strengthening it breaks nothing.

**Finding S2 — same pattern, milder: `coherence_nonneg` (line 294) and
`coherence_zero_iff_diagonal` (line 298) carry the hypothesis `support_le ρ (pinching ρ)`,
which holds for every ρ** (`support_le_pinching`). The module itself discharges it at lines
325, 336, and 378. These two statements could be hypothesis-free — and the inconsistency is
visible within the file, since `coherence_bound` (line 303) is already stated without it.

**Finding S3 — stale/contradictory documentation that a hostile reviewer will trip on:**
- The module header (lines 10–12) still says "The difficult analytic and variational facts
  are explicit axioms until they can be retired" — false since the discharge campaign; the
  module has zero axioms and the kernel check confirms full unconditionality.
- Lines 344, 354–355, 364 call `coherence_monotone_incoherent` "the axiom" (three times) —
  it is a theorem; the comments predate its discharge.
- Cross-doc mismatch: `axiom-surface.md` §5 and PROOF_STATUS say
  `relative_entropy_pinching_eq_entropy_diff` was "deleted 2026-07-02", yet a live proved
  theorem with that exact name is at PinchingEntropy:550 and is used here (line 305). What
  was deleted was evidently the *axiom* version; the docs should say "replaced by a proved
  theorem," not "deleted."
- (Out of module, but load-bearing for it:) the docstring of
  `relative_entropy_real_nonneg_of_support` (PinchingEntropy:1073–1076) still reads "Kept as
  an EXPLICITLY SCOPED axiom" above a completed proof.

**What I checked and found sound:** the spectral construction of `canonical_state` (weights
positive, sum to 1, unitary conjugation preserves trace/PosDef); the cfc composition step in
`canonical_matrix_log` (log applied only on the positive Gibbs spectrum); the junk-convention
reconciliation in `trace_self_log_eq_neg_entropy`; the `β > 0` guards being present exactly
where the algebra needs `β ≠ 0`; `support_le_canonical` (PosDef ⇒ trivial kernel);
`coherence_monotone_incoherent`'s textbook proof structure including both support-condition
discharges; and the non-vacuity witness pair for the MIO hypothesis class. `#print axioms`
already guards the two witnesses in-file (lines 380–381). **No vacuous theorem, no
zero/one stub definition, no junk-value artifact reachable in any exported statement.**

## 3. Axiom-reduction opportunities

No axioms in this module, and — kernel-checked — no *inherited* axiom either. The
tightening opportunities are all hypothesis-level:

1. **Discharge `h_coherence_def`** in `coherent_free_energy_surplus` against
   `relative_entropy_pinching_eq_entropy_diff` (already in scope from `PinchingEntropy`).
   Nothing has to line up — it is the identical statement; this is a 1-hypothesis deletion
   plus a `have`.
2. **Drop the `support_le` hypotheses** of `coherence_nonneg` / `coherence_zero_iff_diagonal`
   using `support_le_pinching`. Again same-statement discharge, zero risk.
3. **Non-vacuity companion for `h_energy_basis`:** a small lemma showing a diagonal `H`
   satisfies `Tr(ρH) = Tr(Δρ·H)` (diagonal-trace computation already available via
   `trace_mul_diagonal_eq` machinery in PinchingEntropy) would document the hypothesis class.
4. The removal note at lines 266–270 (the false `max_entropy_at_fixed_energy`) correctly
   identifies the true Jaynes statement as future work; `MaxEntCanonical` already proves the
   fixed-β entropy-dominance form, so this module owes nothing further.
5. External trust note for the submission packet: `coherence_monotone_incoherent` rests on
   the physlib DPI (`sandwichedRenyiEntropy_DPI_eq_one` via `PhyslibBridge`). That is proved
   code, not an axiom, but it is part of the trusted base and should be named in the
   overview docs alongside Mathlib.

## 4. Legibility / teaching notes

The module is comparatively readable — the private-lemma ladder (`canonical_weight` →
`canonical_matrix` → PosDef/trace → `canonical_state` → crux log lemma → entropy/energy
relation → Gibbs identity → variational principle) is a genuine step-by-step argument, and
the "crux lemma" labeling helps. Top improvements, in order:

1. **Deduplicate the affine-log trace expansion.** `canonical_entropy_eq` (lines 253–264)
   and `relative_entropy_gibbs_identity` (lines 447–456) contain the same 10-line
   `hexpand`/`hre` block expanding `Tr(ρ·(−βH − (log Z)·1))` and taking real parts. Extract
   one named lemma ("trace of a state against an affine Hermitian combination is the affine
   combination of energy and 1") and both proofs shrink to a few meaningful lines. This is
   the single highest-value legibility change.
2. **Fix the stale header and "axiom" comments** (S3): for a teaching artifact, the header
   should now *lead* with "this module is fully proved and inherits no axiom — kernel
   checked," and the witness section should say "the theorem," not "the axiom."
3. **Unitary-coercion noise:** the repeated
   `(V : Matrix (Fin n) (Fin n) ℂ)` casts (worst at lines 210–231 and 391–413) roughly
   double the visual weight of otherwise simple conjugation algebra. A local
   `set V' : Matrix (Fin n) (Fin n) ℂ := ↑V` (or local notation) per proof would let the
   reader see `V * X * star V'` shapes at a glance.
4. **Label the definitional theorems as such.** `thermodynamic_identity` (line 484) is
   proved by `rfl` and `canonical_coherence_bound` (line 311) is a one-line specialization.
   Both are fine as reader-facing API, but their docstrings should say "definitional
   restatement / convenience instance" so a reviewer does not go hunting for content.
5. **Pin the headline with `#print axioms`** on the main exports (Gibbs identity,
   variational principle, coherence monotonicity), matching the existing practice for the
   witnesses — it turns this review's kernel check into a permanent in-file regression guard.
6. Minor: move the witness block (lines 344–381) after the partition-function material, or
   give it its own section header at the end — it currently interrupts the canonical-state
   thread.

## 5. Verdict

This module is in good shape — the best state a reviewed module can honestly be in: every
public theorem is kernel-verified to rest on nothing beyond Lean's three standard axioms
(it does not even inherit the framework's remaining 4), the Gibbs state is a real spectral
construction rather than a stub, and no junk-value artifact is reachable in any exported
statement. The genuine findings are about statements *underselling* the framework:
(1) **do first** — strengthen `coherent_free_energy_surplus` by discharging the redundant
`h_coherence_def` (it assumes a theorem the framework proves) and resolving the dead `h_β`,
and drop the always-true `support_le` hypotheses from `coherence_nonneg` /
`coherence_zero_iff_diagonal`; (2) **do with it** — fix the stale module header and
"the axiom" comments, and reconcile the axiom-surface/PROOF_STATUS wording about
`relative_entropy_pinching_eq_entropy_diff` ("deleted" → "replaced by a proved theorem"),
since these are exactly the tripwires an external PhysLean reviewer will hit; (3) **do
later** — the legibility pass: extract the shared affine-log trace-expansion lemma used by
`canonical_entropy_eq` and `relative_entropy_gibbs_identity`, tame the unitary-coercion
noise, and add `#print axioms` guards on the main exports to lock in the unconditional
status this review verified.
