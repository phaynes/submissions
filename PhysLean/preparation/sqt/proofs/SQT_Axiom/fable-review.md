# Fable review — `Proofs/SQT_Axiom.lean` (143 lines, 3 axioms)

Reviewed against: `PROOF_STATUS.md` (2026-07-02), `axiom-surface.md`, `proof-map.md`,
`control/boundary.json`. Source cross-checked against `PhyslibBridge.lean`,
`BasicDefinitions.lean`, `PinchingEntropy.lean`, `CPTPEmbedding.lean`, `Correspondence.lean`.
Analysis only; no source edits.

## 1. What this module proves

`SQT_Axiom.lean` is the terminal assumption surface for the thermodynamic (A3) leg of the
proof product. It contains:

- `GKLSGenerator` (l. 22–24): pure data — a Hermitian `hamiltonian` plus a `List` of Lindblad
  operators. No Lindbladian superoperator is defined anywhere; "GKLS" is nominal data.
- `IsUnitalGKLS` (l. 32–39): the real dissipator-unitality predicate `∑ LᵢLᵢᴴ = ∑ LᵢᴴLᵢ`.
- The 3 axioms: `gkls_evolution` (l. 48–49, an opaque evolution *function*),
  `spohn_entropy_production` (l. 54–57, `ΔS ≥ 0` for unital generators, `t > 0`), and
  `entropy_monotone_gkls` (l. 59–63, `S` non-decreasing in time for unital generators).
- A machine-checked satisfiability block (l. 65–115): `const_evolution` witnesses that the
  axiom trio is jointly satisfiable (`gkls_axiom_surface_satisfiable`, l. 95–104), and
  `isUnitalGKLS_witness` (l. 111–113) shows the unitality hypothesis class is non-empty.
- Three corollaries (l. 123–141): `second_law_quantum` and two restatements of the Spohn
  axiom (`entropy_production_nonneg`, `entropy_rate_nonneg`).

**Blast radius: zero.** No module imports `SQT_Axiom` (verified by grep across
`verification/lean`; the module builds only via the lakefile's `.submodules` glob). Every
other module's theorems are independent of these 3 axioms. The module is a *statement
product* — the second-law corollary is the deliverable, not a dependency. This containment
is worth stating explicitly in the review docs; it is a strong property.

## 2. Soundness review

**No unsoundness found.** What I checked, and what I found:

1. **Consistency of the trio.** The risk pattern here (opaque axiom-declared function +
   two axioms asserting properties of it) is joint unsatisfiability. The module addresses
   exactly this: `const_evolution` (l. 76–77) inhabits the type and satisfies both property
   statements verbatim (`const_evolution_spohn` l. 80–84 closes with `S(ρ) − S(ρ) = 0 ≥ 0`;
   `const_evolution_entropy_monotone` l. 87–92 is `le_refl`). I verified the witness proofs
   do not reference the axioms themselves (the `#print axioms` directives at l. 106/115
   confirm this at build time). The conservativity claim in the comment block (l. 65–73) is
   the standard meta-theoretic reading and the module honestly confines the machine-checked
   part to the existential. This block is genuinely good hygiene — most axiom surfaces do
   not come with checked satisfiability witnesses.

2. **The quantities are real, not stubs.** `von_neumann_entropy` (`PhyslibBridge.lean:21–24`)
   is the honest spectral quantity `−∑ λᵢ log λᵢ` with an explicit `if λᵢ = 0 then 0` guard —
   this is the standard `0·log 0 = 0` entropy convention, *not* a junk-value artifact (the
   guard agrees with the limit). `DensityMatrix` (`BasicDefinitions.lean:25–29`) is honest
   Hermitian + PSD + trace-1. `entropy_production` (l. 51–52) is a plain `ℝ` difference of
   finite entropies — no `EReal`/junk edge. So the axioms assert something with real content
   about their arguments, modulo the known evolution weakness below.

3. **`IsUnitalGKLS` is the right predicate.** `L(I) = 0 ⟺ ∑ LᵢLᵢᴴ = ∑ LᵢᴴLᵢ` (the
   Hamiltonian commutator vanishes on `I` automatically), which is equivalent to unitality
   of the generated semigroup. Non-vacuity is witnessed (l. 111–113); the empty-list case
   (pure Hamiltonian evolution) correctly counts as unital. Hypotheses `0 < t` and
   `0 ≤ s ≤ t` are satisfiable and necessary (a reversible evolution at negative time would
   falsify monotonicity, so the guard is not decorative).

4. **`gkls_evolution` — sound-but-weak, honestly flagged.** The in-code NOTE (l. 41–47)
   states the situation exactly: the axiom is a total-function declaration whose type is
   inhabited, so it cannot prove `False`, but it ties the output to nothing. Consequently
   `spohn_entropy_production` / `entropy_monotone_gkls` are assumptions about a *nominal*
   evolution, and `second_law_quantum` says nothing about actual Lindblad dynamics until
   the generator gets a defining law. This matches `boundary.json` (`weak_but_sound:
   ["gkls_evolution"]`) and `axiom-surface.md`. There is no hidden overclaim: the weakness
   is documented at the declaration site, which is where a reviewer will look.

5. **Faithfulness of the unital restriction to Spohn 1978.** Spohn's theorem is the
   derivative form `σ(ρ) = −Tr[L(ρ)(log ρ − log ρ_stat)] ≥ 0` for a quantum dynamical
   semigroup with stationary state `ρ_stat`. For a *unital* semigroup, `ρ_stat = I/n`, and
   `D(ρ₀‖I/n) − D(ρ_t‖I/n) = S(ρ_t) − S(ρ₀)` exactly (the `log n` terms cancel), so the
   axiomatized `ΔS ≥ 0` is precisely the *integrated* Spohn entropy production relative to
   the maximally mixed stationary state. Verdict: **faithful as an honest specialization,
   and strictly weaker than the cited theorem** — the safe direction for an assumption.
   Two doc-level caveats (not soundness defects): (a) a reviewer expecting Spohn's σ (the
   relative-entropy derivative) will read `entropy_production := ΔS` as a misnomer unless
   the cancellation identity above is recorded in a docstring; (b) the unital `ΔS ≥ 0` form
   also follows from data processing alone (Lindblad 1975 / Uhlmann), which matters because
   that is the discharge path (§3) — the citation could note both.

6. **The two property axioms are genuinely independent today.** Because the evolution is
   opaque, `entropy_monotone_gkls` does **not** follow from `spohn_entropy_production`
   (nothing relates `ev L ρ s` to `ev L ρ t`), nor vice versa (nothing says
   `ev L ρ 0 = ρ`). So carrying both is currently necessary, and the "expected to collapse"
   note (l. 47) is a correct statement about the future, not the present. §3 makes the
   collapse mechanics precise.

Not found: vacuous hypotheses, `True`-shaped goals, zero/one stubs inside proof-carrying
statements, junk-value exploits, or any way for the trio to strengthen or contradict the
rest of the development (impossible given the const model plus zero importers).

## 3. Axiom-reduction opportunities

The module-specific question — *can spohn/entropy_monotone collapse to one lemma once the
generator gets a real defining law?* — has a precise **yes**, in two tiers.

**Tier 1 (collapse to one thermodynamic axiom, lands with the defining law).** The two
laws needed are the semigroup identities:

- *initial condition:* `ev L ρ 0 = ρ`
- *composition:* `ev L ρ (s + u) = ev L (ev L ρ s) u` for `s, u ≥ 0`

Given **composition**, `entropy_monotone_gkls` follows from `spohn_entropy_production`
(for `s < t`, apply Spohn at state `ev L ρ s` with time `t − s > 0`; `s = t` is `le_refl`).
Given the **initial condition**, Spohn follows from monotonicity (take `s := 0`). So keep
exactly one — `spohn_entropy_production`, the citable one — and derive the other. If
`gkls_evolution` is realized as a superoperator exponential on vectorized states, both laws
are free (`Matrix.exp_zero`, `Matrix.exp_add_of_commute`; `s•L̂` and `u•L̂` commute), so the
collapse can land in the same change that introduces the defining law. Net: 3 axioms → 2.

**Tier 2 (discharge both property axioms; 3 → 1; mostly in-development).** The development
already contains almost everything needed to make the unital second law a *theorem*:

- `relative_entropy_monotone` is already **proved** via physlib DPI
  (`PinchingEntropy.lean:2158`, hypothesis `support_le ρ σ`).
- `support_le_maximally_mixed` is already proved (`PinchingEntropy.lean:2259`) — against
  `σ = I/n` the support condition holds automatically, so the framework's known junk-value
  pitfall (`log 0 = 0` off-support) *cannot bite* on this path.
- `CPTPMap.is_unital` (`CPTPEmbedding.lean:290`), `unital_kraus_condition` (:300),
  `CPTPMap.compose` (:336), and `CPTPMap.id_unital` (:408) all exist.
- **The one missing bridge lemma:** the general identity
  `relative_entropy_real ρ (maximally_mixed n) = Real.log n − von_neumann_entropy ρ`.
  Only the idempotent special case exists today (`D_idem_maximally_mixed`,
  `PinchingEntropy.lean:2275–2277`, private). The general case is a modest spectral
  computation (`matrix_log ((1/n)•I) = −(log n)•I`, then trace algebra); the tooling that
  proved the idempotent case suffices. One convention to check while proving it: that
  `Tr(ρ log ρ).re = −S(ρ)` under `matrix_log`'s zero-eigenvalue convention (the `λ = 0`
  terms vanish on both sides, so this should be mechanical).

With that lemma: for any unital CPTP `Φ`,
`S(Φρ) = log n − D(Φρ‖I/n) = log n − D(Φρ‖Φ(I/n)) ≥ log n − D(ρ‖I/n) = S(ρ)`
(unitality transported to `DensityMatrix` equality via `DensityMatrix.matrix_ext`,
`BasicDefinitions.lean:34`). Then replace all three axioms with **one** structural axiom:
existence of the GKLS CPTP semigroup — e.g. `gkls_semigroup : GKLSGenerator n → ℝ≥0 →
CPTPMap n` with fields `at_zero = CPTPMap.id`, composition via `CPTPMap.compose`, and
`unital_of : IsUnitalGKLS L → ∀ t, (at t).is_unital`. Both `spohn_entropy_production` and
`entropy_monotone_gkls` become theorems, `gkls_evolution` stops being vacuous, and the one
remaining axiom asserts a true, citable mathematical fact (the GKLS-form-generator ⇒ CPTP-
semigroup direction) rather than a thermodynamic inequality — a strictly better surface.

Full discharge of even that last axiom means formalizing complete positivity of `e^{tL}`
(Trotter/Kraus-limit argument) — genuinely substantial, reasonable to leave as the single
axiom, and a plausible upstream physlib target to propose.

## 4. Legibility / teaching notes

The satisfiability-witness block (l. 65–115) is exemplary teaching material and should be
kept prominent. The issues are around it:

1. **Dead code in the most-scrutinized module.** `WaveFunction` (l. 117–119) and the
   `Hamiltonian` abbrev (l. 121) are used nowhere — in this module or anywhere (nothing
   imports `SQT_Axiom` at all). Unused definitions in the axiom-carrying module cost
   reviewer trust disproportionately; delete them or move them where they are used.
2. **Unused import.** `import Proofs.Correspondence` (l. 3) — no `SQC` identifier is
   referenced; the docstring cross-reference does not need the import. Drop it, or replace
   it with an explicit statement of the intended future SQC↔GKLS link.
3. **One fact wearing three names.** `entropy_production_nonneg` (l. 131–135) and
   `entropy_rate_nonneg` (l. 137–141) are the Spohn axiom restated modulo unfolding;
   `second_law_quantum` (l. 123–129) is the same content in second-law form. A reader may
   count three results where there is one assumption. Keep `second_law_quantum` as the
   single named export and demote the others. `entropy_rate_nonneg` is also **misnamed** —
   it is a finite difference, not a rate `dS/dt`; in a teaching artifact this borders on
   overclaim. Rename (e.g. entropy *difference*) or remove.
4. **Earn the name "entropy production" in a docstring.** On l. 51, record the identity
   `D(ρ₀‖I/n) − D(ρ_t‖I/n) = ΔS` (unital stationary state), so the definition is visibly
   the integrated Spohn quantity rather than an arbitrary rebranding of `ΔS`.
5. **Split the conjunction.** `h_order : 0 ≤ s ∧ s ≤ t` (l. 61) → two named hypotheses;
   idiomatic and easier to reference in prose.
6. **Jargon.** "Restart-wave interface" (l. 8) is project-internal; replace with a plain
   statement of the module's role (terminal A3 assumption surface, zero importers).

## 5. Verdict

This module is in good shape: no unsound statement, no junk-value exploit, the one known
weakness (`gkls_evolution` unconstrained) is flagged at the declaration site and in the
ledger, the unital restriction on Spohn is a faithful (strictly weaker) specialization of
Spohn 1978, and the machine-checked satisfiability witnesses are above-standard hygiene.
Ranked follow-ups: **(1)** give the evolution its defining law and collapse the two
property axioms to one (Tier 1, §3) — this is the highest-value content upgrade and
answers the module's own TODO; **(2)** prove the general `D(ρ‖I/n) = log n − S(ρ)` bridge
lemma and take Tier 2 (3 axioms → 1 structural axiom) — surprisingly close, since DPI and
the support lemma are already proved in-development; **(3)** legibility polish (dead
`WaveFunction`/`Hamiltonian`, unused `Correspondence` import, deduplicate/rename the three
corollaries, docstring the entropy-production identity) — do after the axiom work, before
external review. Items 1–2 are content upgrades, not soundness fixes; nothing here blocks
the current conditional-proof claim.
