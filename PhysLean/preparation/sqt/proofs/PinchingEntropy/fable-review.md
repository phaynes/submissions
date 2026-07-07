# Fable review — `Proofs/PinchingEntropy.lean`

Reviewed: 2026-07-08. Source: `verification/lean/Proofs/PinchingEntropy.lean` (2570 lines, 1 axiom).
Method: full read of the module; cross-check against `PROOF_STATUS.md`, `axiom-surface.md`,
`proof-map.md`, `control/boundary.json`; greps for axiom consumers; inspection of the vendored
physlib pin (`.lake/packages/Physlib`) and the submitted PhysLean packet; and a fresh
kernel-level `#print axioms` run on seven key theorems (results below). Analysis only — no
source edits.

---

## 1. What this module proves

This is the entropy/relative-entropy core of the framework. Six blocks:

1. **Basic entropy facts** — `entropy_nonneg` (39), `entropy_max_at_mixed` (53, Jensen via
   `Real.concaveOn_negMulLog`), `entropy_pure_zero` (117, rank-1 spectral argument).
2. **Fixed-basis pinching (dephasing)** — `pinching` (214) keeps the diagonal;
   `relative_entropy_pinching_eq_entropy_diff` (550): relative entropy of coherence equals the
   entropy gain; the Pythagoras identity against any diagonal reference
   (`relative_entropy_pinching_add_of_diagonal`, 638); `pinching_entropy_inequality` (1198).
3. **Relative entropy and Klein's inequality, proved from scratch** — `support_le` (281,
   kernel inclusion), the finite value `relative_entropy_real` (314, with the `log 0 = 0` junk
   convention explicitly documented), the honest EReal `relative_entropy` (320, `⊤` off
   support). Klein `relative_entropy_real_nonneg_of_support` (1077) is proved via spectral
   decomposition + doubly-stochastic eigenvector-overlap matrix + per-row Jensen + a finite
   Gibbs inequality; its full **equality case** `relative_entropy_eq_zero_iff` (1410)
   reconstructs `ρ = σ` from the two Jensen tightnesses. `entropy_concave` (1314) follows.
4. **The one axiom + its own refutation** — `not_relative_entropy_jointly_convex_unconditional`
   (1833) is a kernel-verified counterexample showing the *unconditional* joint convexity of the
   finite value is false (junk `log 0 = 0` forces `log 2 ≤ 0`); the scoped axiom
   `relative_entropy_jointly_convex` (1852) is the on-support (Lieb) form.
5. **Multipartite facts and DPI via the physlib bridge** — `entropy_subadditive` (262),
   `strong_subadditivity` (1861), `araki_lieb_triangle` (1880) reduce through
   `toMState/toMStatePair/toMStateTriple` to physlib's `Sᵥₙ_*` theorems;
   `relative_entropy_monotone` (2158) is discharged via physlib's
   `sandwichedRenyiEntropy_DPI_eq_one` using a small conversion layer
   (`support_le_toMState_ker` 2115, `qRelativeEnt_ne_top_of_support` 2137,
   `qRelativeEnt_toReal_eq_relative_entropy_real` 2147).
6. **Audit infrastructure** — junk-closure lemmas showing the scoped statements never quantify
   over a junk case (`support_le_cptp` 2023, `support_le_mixture_of_support_le` 2066), the
   dephasing channel as a concrete CPTP map realizing `pinching` (2182), and non-vacuity
   witnesses with `#print axioms` guards (2250–2568).

## 2. Soundness review

**No unsound theorem found.** What I checked, specifically:

- **Klein chain (1077–1182).** The support hypothesis enters exactly where the junk convention
  would bite: `support_zero_eigen_overlap_mul_eq_zero` (809) gives `q_j = 0 → p_i·P_ij = 0`, so
  every `log(q_j)` with nonzero weight is a log of a positive number; rows with `p_i = 0`
  contribute zero to both sides; the Gibbs step (`finite_gibbs_nonneg`, 975) gets
  `r_i > 0` whenever `p_i > 0` from row-stochasticity + the support condition. No junk value
  reaches a load-bearing position.
- **Equality case (1410–1616).** The overlap fact `hoverlap` (1550) is derived for *all* `i`,
  including `p_i = 0` (via `r_i = p_i = 0` forcing `q_j = 0` on overlapping columns), before the
  entrywise reconstruction `W·diag q·W* = diag p` — the case split is complete. The final
  `cases ρ; cases σ; simp_all` is legitimate (the non-matrix fields are propositions).
- **`entropy_concave` (1314).** Sign algebra checked by hand: `0 ≤ p·D(ρ‖τ) + (1−p)·D(σ‖τ)`
  expands to `S(τ) ≥ p·S(ρ) + (1−p)·S(σ)` correctly; boundary cases `p ∈ {0,1}` collapse at the
  matrix level and use entropy congruence, so no support hypothesis is smuggled in.
- **The refutation (1833) and axiom (1852).** The counterexample is kernel-checked
  (`#print axioms` at 1844). The scoped axiom is **true**: given `support_le` on both pairs, both
  RHS terms are honest values, `support_le_mixture_of_support_le` (2066) proves the LHS pair is
  also on-support, and `qRelativeEnt_toReal_eq_relative_entropy_real` (2147) proves the local
  finite value coincides with physlib's Umegaki value there — so the statement is precisely
  on-support Lieb joint convexity, and the non-vacuity witness (2303) shows the hypotheses are
  satisfiable with both sides nonzero. It is honestly scoped, and stronger scoping than needed is
  the safe direction for an axiom.
- **Kernel-level axiom trails (fresh run, this review).** `#print axioms` on
  `strong_subadditivity`, `entropy_subadditive`, `araki_lieb_triangle`,
  `relative_entropy_monotone`, `relative_entropy_real_nonneg_of_support`,
  `relative_entropy_eq_zero_iff`, `entropy_concave` each report exactly
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no project axiom. The physlib SSA/DPI
  theorems this module leans on are genuinely proved in the pinned commit.

Three findings, none a proof defect:

**F1 — The axiom has zero consumers.** `relative_entropy_jointly_convex` is declared, refuted-
then-rescoped, witnessed — and never *applied* anywhere in the Lean development (repo-wide grep;
confirmed by the clean axiom trails above). The conditional proof product as built today does not
depend on Lieb's theorem at all. This is favorable, but the surface documents
(`axiom-surface.md`, the writeup) present it as a load-bearing assumption; they should state
plainly that it is currently a forward-declared interface, not a dependency of any proved
corollary. It also means the discharge in §3 is pure surface reduction with no downstream risk.

**F2 — Stale docstring on a *theorem* claiming to be an *axiom* (lines 1073–1076).**
`relative_entropy_real_nonneg_of_support` carries the docstring "the remaining honest gap …
(~250–350 LOC, scheduled). Kept as an EXPLICITLY SCOPED axiom" — but the declaration below it is
a complete ~105-line proof (and its axiom trail is clean). For an artifact destined for external
review, a self-description that contradicts the code is the most damaging kind of documentation
error: it invites the reader to distrust every other honesty annotation. Same family, smaller:
the module header (16–23) still describes the file as recording "obligations as explicit axioms"
(one remains); witness docstrings at 2473 and 2496 say "proven WITHOUT the axiom" for
`entropy_subadditive`/`araki_lieb_triangle`, which are now theorems (there is no such axiom); the
docstring at 1206 says `von_neumann_entropy_eq_of_matrix_eq` uses the "same technique as
`pinching_entropy_inequality`: match characteristic-polynomial roots" — `pinching_entropy_inequality`
uses Klein, not charpoly roots. Also cross-doc: `PROOF_STATUS.md`/`axiom-surface.md` §5 say
`relative_entropy_pinching_eq_entropy_diff` was "deleted (2026-07-02)", yet a proved theorem of
exactly that name exists at line 550 (the *axiom* was deleted; the theorem for the real
fixed-basis pinching is true — I verified the identity). Say "axiom deleted, later reproved as a
theorem" to spare a diligent reviewer the alarm.

**F3 — Latent gate blind spot: dependency `sorryAx` laundering.** The pinned physlib commit
already *declares* `qRelativeEnt_joint_convexity` — as a `@[sorryful] … := by sorry` stub
(`.lake/packages/Physlib/QuantumInfo/Entropy/Relative.lean:2118–2122`). Nothing uses it today,
but if a future edit "discharged" the local axiom by calling the stub, `lake build` would stay
green and the local snapshot (`sorries_or_admits=0` counts local files) would not flag it; only a
transitive `#print axioms` shows `sorryAx`. Recommend adding a boundary-gate check that the
axiom trail of every exported theorem contains no `sorryAx` (the module's own `#print axioms`
lines print the evidence but nothing fails on it). This is the same genus as the C7 junk-scope
blind spot the project already closed.

Minor citation note: `axiom-surface.md` cites the axiom to "Lieb–Ruskai 1973, DOI
10.1063/1.1666274" (the SSA paper). Joint convexity of the Umegaki relative entropy is standardly
Lieb 1973 (*Adv. Math.* 11, 267 — the concavity theorem) with the convexity form usually credited
to Lindblad 1974. Worth tightening before external eyes.

## 3. Axiom-reduction opportunities — discharging `relative_entropy_jointly_convex` against PhysLean PR #1378

This is the centerpiece. Everything lines up unusually well, because the conversion layer built
for `relative_entropy_monotone` (2114–2176) is exactly the layer this discharge needs.

**The upstream statement** (identical in the submitted packet
`submissions/PhysLean/submitted/Proof-Joint-convexity-of-the-Umegaki-quantum-relative-entropy/proof/qRelativeEnt_joint_convexity.lean:150`
and, verbatim, as the `@[sorryful]` stub already present in the pinned physlib at
`QuantumInfo/Entropy/Relative.lean:2119` — the PR replaces the sorry):

```
theorem qRelativeEnt_joint_convexity :
    ∀ (ρ₁ ρ₂ σ₁ σ₂ : MState d), ∀ (p : Prob),
      𝐃(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) ≤ p * 𝐃(ρ₁‖σ₁) + (1 - p) * 𝐃(ρ₂‖σ₂)
```

with `𝐃 : MState d → MState d → ℝ≥0∞` (Relative.lean:1497) — *unconditional*, because `⊤`
absorbs the off-support junk that forced the local rescoping. The local axiom is the scoped,
real-valued shadow of this; the shim's job is pure statement transport.

**What already lines up (verified against the pinned dependency):**

- `Prob := { p : ℝ // 0 ≤ p ∧ p ≤ 1 }` (`ClassicalInfo/Prob.lean:36`) — the local hypothesis
  `h_p : 0 ≤ p ∧ p ≤ 1` *is* the subtype property; `(⟨p, h_p⟩ : Prob)` is literal.
- Mixture order matches: physlib `p [τ₁ ↔ τ₂]` has `.M = p • τ₁.M + (1−p) • τ₂.M` (packet lemma
  `mix_M_eq_weighted_sum`), and `density_matrix_mixture` (224) is
  `(p:ℂ) • ρ₁ + ((1−p:ℝ):ℂ) • ρ₂` — weight `p` on the first argument on both sides; RHS
  coefficients also match.
- `MState` is `@[ext]` with matrix-level `ext_m` (`States/Mixed/MState.lean:62,124`), so the one
  new bridge lemma is provable by `ext` + the ℝ-smul vs ℂ-cast-smul bridge already used inside
  `density_matrix_mixture.positive` (239–247).
- Support condition: `support_le_toMState_ker` (2115) translates `support_le` into exactly the
  `σ.M.ker ≤ ρ.M.ker` form physlib uses; finiteness comes from `qRelativeEnt_ne_top_of_support`
  (2137); value agreement on support from `qRelativeEnt_toReal_eq_relative_entropy_real` (2147);
  the LHS pair is on-support by `support_le_mixture_of_support_le` (2066) — all four already in
  this module.
- Coercion glue exists upstream: `Prob.coe_one_minus` (Prob.lean:177), `Prob.zero_lt_coe` (:162);
  the Prob→ℝ≥0∞ path in the RHS products is the `(p : NNReal) : ENNReal` coercion the PR proof
  itself manipulates.

**The shim, concretely** (replace `axiom` at 1852 with a `theorem` of the *identical* statement):

1. New bridge lemma (~15 lines), the only genuinely new content:
   `toMState_mixture : toMState (density_matrix_mixture ρ σ p h_p) = (⟨p, h_p⟩ : Prob) [toMState ρ ↔ toMState σ]`
   — by `MState.ext_m`; entrywise both matrices are `p·ρ i j + (1−p)·σ i j` after `Algebra.smul_def`.
2. Instantiate `qRelativeEnt_joint_convexity` at `d := Fin n`, states `toMState ρᵢ, toMState σᵢ`,
   `P := ⟨p, h_p⟩`; rewrite both mixtures with (1).
3. Finiteness: `hne₁/hne₂ := qRelativeEnt_ne_top_of_support _ _ h₁/h₂`; RHS `≠ ⊤` (finite
   coefficients times finite entropies); LHS `≠ ⊤` by `ne_top_of_le_ne_top`.
4. `ENNReal.toReal_mono`, then distribute `toReal` with `ENNReal.toReal_add` (both summands
   finite) and `ENNReal.toReal_mul` (unconditional); collapse the Prob coercions with
   `Prob.coe_one_minus` and the NNReal/ENNReal `toReal` simp set.
5. Rewrite the three `toReal 𝐃` values into `relative_entropy_real` via
   `qRelativeEnt_toReal_eq_relative_entropy_real` with `h₁`, `h₂`, and
   `support_le_mixture_of_support_le … h₁ h₂`.

Estimated ~15 + ~50 lines. Then: delete the axiom, ledger row moves to the discharged file,
`boundary.json` goes 4 → 3, and the *entire analytic core becomes unconditional*. Update the
1846–1851 docstring ("Lieb's concavity theorem is absent from Mathlib" — true of Mathlib, but no
longer the operative fact) and `axiom-surface.md`.

**Two operational paths, one hazard:**

- **Path A (wait for merge, bump the pin).** The pinned `Physlib` (`lakefile.lean` @ `eb547a5c`)
  already contains the statement as a stub, so there is no statement-drift risk unless upstream
  review edits it — keep the packet's statement and the upstream declaration diffed until merge.
  Note the PR moves the theorem to `Entropy/DPI.lean` (packet header; commit `720c9fff`), which
  the bridge already imports. The real cost is pin motion: bumping physlib may force a mathlib
  bump (dev pins mathlib `fabf563a` separately) and a full rebuild of all 11 modules.
- **Path B (vendor now).** The pinned commit already has every deep ingredient the 222-line
  packet proof needs: `sandwichedTraceFunctional_jointly_convex` (DPI.lean:568),
  `sandwichedRelRentropy_eq_log_traceFunctional` (:78), `sandwichedTraceFunctional_pos` (:100),
  `HermitianMat.ker_weighted_sum_le` (:542), `Prob.zero_lt_coe`, `Prob.coe_one_minus`. Only the
  PR-added helpers (`Mixable.mix_one`, the `ne_top_iff` twins, and the α→1⁺ limit lemmas in the
  packet) would be vendored into a local `Proofs/LiebLocal.lean`. This discharges the axiom
  *today* with a clean kernel trail, at the cost of ~220 vendored lines to delete after the merge.
- **Hazard (do not do this):** shim against the *current* pinned `qRelativeEnt_joint_convexity`.
  It is `@[sorryful]`; the build stays green and only `#print axioms` reveals the `sorryAx` (see
  F3). Any discharge PR should include the `#print axioms relative_entropy_jointly_convex` output
  in its evidence.

Since the axiom has no consumers (F1), a degenerate third option is deletion — instant 4 → 3 —
but that forfeits the stated Lieb interface; the shim is strictly better and cheap.

## 4. Legibility / teaching notes

The file is *auditable* (the honesty annotations, refutation, witnesses and `#print axioms`
guards are exemplary) but not yet *readable end-to-end*. Top items, in value order:

1. **The Klein setup is duplicated wholesale.** Lines 1080–1182
   (`relative_entropy_real_nonneg_of_support`) and 1415–1509 (`relative_entropy_eq_zero_iff`)
   repeat ~95 lines verbatim: the `U, V, W, P, p, q, r` cast and the seven facts
   (`hp_nonneg … hr_pos_of_hp_pos, hrow_log_le, hcross_le, hgibbs, hrel, hlower`). Extract a
   named private setup (a structure `KleinData` carrying `p q P r` and the proved facts, or one
   lemma returning the conjunction) so the equality-case proof reads as "run Klein, squeeze both
   Jensen steps, reconstruct" — which is exactly its docstring, currently buried under the
   duplication.
2. **`entropy_concave` re-derives an existing lemma three times.** Lines 1358–1381 inline the
   proof of `trace_self_log_eq_neg_entropy` (434) for ρ, σ, τ — 24 lines that should be three
   citations. Same disease in miniature: the negMulLog↔entropy conversion appears at 59–65 and
   again at 1243–1257, and `density_eigenvalues_sum_eq_one` (334) is re-proved inline at 66–79
   and 134–146 because those theorems precede it in the file — hoist the private lemmas to the
   top of the entropy block.
3. **Twin lemmas duplicate their scaffolding.** `weighted_log_le_…`/`weighted_log_eq_…`
   (876–973) share the filter-to-positive-support boilerplate (`t, hw_sum_t, hlog_filter,
   hq_filter`), and `finite_gibbs_nonneg`/`finite_gibbs_eq_zero` (975–1071) share the
   `log x ≤ x − 1` term bound. One shared private lemma each.
4. **Coercion noise.** `(U : Matrix (Fin n) (Fin n) ℂ)` is spelled out hundreds of times in the
   spectral sections (668–865). A local `abbrev` per section (or `set`) would shrink these proofs
   by a third and make the `W = U*V` doubly-stochastic-overlap idea visible.
5. **Stale self-description** (F2 above) — for a teaching artifact this is also the cheapest
   legibility fix: rewrite the module header as a current map of the six blocks (the structure in
   §1 of this review is essentially it), and fix the four stale docstrings.

## 5. Verdict

This module is in good shape: the hard analysis (Klein with equality case, concavity, the
pinching Pythagoras identity) is genuinely proved with the junk convention handled honestly at
every load-bearing point, the single axiom is true, faithfully scoped, witnessed non-vacuous —
and, notably, not yet used by anything. Ranked follow-ups: **(1)** discharge
`relative_entropy_jointly_convex` against the PhysLean result via the shim in §3 (one ~15-line
`toMState_mixture` bridge plus ~50 lines of ENNReal glue; all other ingredients already exist in
this module), choosing Path A (pin bump after merge) or Path B (vendor the packet helpers now),
and in the same change add the `sorryAx`-trail gate from F3 so the sorryful upstream stub can
never be laundered in silently; **(2)** fix the stale docstrings — above all the theorem at 1073
that still calls itself an axiom — trivial edits with outsized credibility value for external
review; **(3)** the §4 deduplication (Klein setup, `entropy_concave` inlines), which is polish and
can wait, but should precede any teaching-facing publication of the file. Item 1 removes the only
axiom in the analytic core and is the single highest-value discharge available to the framework.
