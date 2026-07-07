# Fable review — cross-module synthesis (2026-07-08)

Overnight, one Fable agent per module produced a soundness + axiom-reduction + legibility
review (in each `proofs/<Module>/fable-review.md`). **These are analysis, not verified
edits** — no `.lean` source was changed. Several agents ran a genuine kernel `#print
axioms` (via `lake env lean`), not just reading; those are marked *kernel-verified* below.

The framework builds green (8632 jobs, 0 sorry/admit, 4 declared axioms). But Fable found
that the honest axiom surface is **larger than the declared 4** — there is at least one
*hidden* assumption carried as a structure field, plus several overstated "proved" claims.
Fix these before this proof is put in front of a PhysLean-caliber reviewer.

---

## A. Soundness findings — do these FIRST (ranked by severity)

### A1. Landauer's principle is assumed, not proved — a HIDDEN assumption (InformationTheory)
**Severity: high. This is the most important finding.**
`ErasureProcess` (`InformationTheory.lean:264`) carries a field
`heat_landauer_bound : heat ≥ (1/beta) * S(initial)` — i.e. **the Landauer bound is baked
into the structure as an axiom**. Every "Landauer" theorem then discharges by
`simpa … using proc.heat_landauer_bound` / `using h_Q`:
- `landauer_qubit_erasure` (l.290), `landauer_maximal_entropy_bit` (l.298),
  `maxwell_demon_resolution` (l.306) take a hypothesis `h_Q : Q ≥ (1/β)·S(ρ)` and conclude
  exactly `… ≥ (1/β)·S(ρ)` — **hypothesis literally equals conclusion**.
- `reversible_vs_irreversible` proves `S(ρ) = S(ρ)` by `rfl`.

**Why it matters:** this is the "merely true"/assume-the-conclusion pattern JTS explicitly
rejects, AND it is **invisible to the 4-axiom count** (a structure field, not an `axiom`),
so `axiom-surface.md`'s "no known-false axiom, surface = 4" claim is currently *incomplete*.
**Action:** either (a) prove Landauer from the entropy/free-energy machinery already in the
framework, or (b) if it stays an assumption, declare it honestly on the axiom surface and
stop calling these theorems proofs of Landauer. Do NOT ship the current form.

### A2. `relative_entropy_jointly_convex` — zero consumers + upstream-sorry laundering hazard (PinchingEntropy)
**Severity: medium-high (integrity, not falsity).** *Kernel-verified sound on-support.*
The axiom has **zero consumers** anywhere in the Lean development, and the pinned physlib
contains the *identical* statement as a `@[sorryful]` stub (`Relative.lean:2122`). So the
local sorry-count gate would not notice that this axiom stands in for an upstream `sorry`.
It is Lieb's theorem on-support (true), so this is a laundering *hazard*, not a false
claim. **Action:** discharge it (see B1) — Fable found the discharge is cheap — or, if kept
short-term, note in-file that it shadows an upstream sorry.

### A3. Overstated "discharged/proved" claims (Correspondence, CPTPEmbedding)
**Severity: medium (honesty of claims).**
- `Correspondence`: `quantumStepDiagonal` (l.137) bakes the Born-rule sum into its
  *definition* while its docstring calls it "the diagonal of the unitary evolution" — no
  lemma connects it to `U diag(p₀) Uᴴ`, so `diagonal_evolution_match` is a one-`simp`
  rewrite, not an evolution law. And `unitary_channel_bistochastic` is claimed "discharged
  here" but `corr_consistency` proves only the *column* half (the row half is elsewhere; no
  module proves two-sided bistochasticity).
- `CPTPEmbedding`: `stinespring_exists` (l.272) is a *deliberately vacuous* axiom, honestly
  documented in-file with zero downstream uses — but `axiom-surface.md`/`proof-map.md` say
  Stinespring was "discharged to a theorem," which misleads a reader into thinking the real
  dilation theorem was proved. It was neither assumed-usefully nor proved; it is unused.
**Action:** correct the wording in the docstrings and in `axiom-surface.md` to match reality.

### A4. Physics-content-as-hypothesis (CoherentFreeEnergy)
**Severity: low-medium.** `coherent_free_energy_surplus` (l.277) takes `h_coherence_def`
as a hypothesis that *duplicates the already-proved* `relative_entropy_pinching_eq_entropy_diff`
(`PinchingEntropy:550`), and `h_β` is dead. So the theorem assumes what it could cite.
**Action:** drop the hypotheses and use the proved theorem directly.

---

## B. Axiom-reduction plan (the discharge paths)

### B1. PinchingEntropy `relative_entropy_jointly_convex` → PhysLean PR #1378 (CHEAP)
Fable's headline result: discharging this against the upstream
`qRelativeEnt_joint_convexity` (your PR #1378) is **unusually cheap**. What lines up:
- `Prob`'s subtype property **is** the axiom's `h_p`;
- mixture orders match;
- the four conversion lemmas are identified: `support_le_toMState_ker`,
  `qRelativeEnt_ne_top_of_support`, `qRelativeEnt_toReal_eq…` (see the PinchingEntropy
  review for the full shim). Blocked only on PR #1378 merging (so the upstream statement is
  a theorem, not a `@[sorryful]` stub). **This removes 1 of 4 declared axioms** and closes
  the A2 laundering hazard at once.

### B2. SQT_Axiom — 3 axioms collapsible toward 1
*Kernel-verified consistent; unital restriction faithful to Spohn 1978.* Fable's precise
finding: with a **semigroup defining law** on the generator, composition alone derives
`entropy_monotone_gkls` from `spohn_entropy_production` (and the initial-condition gives the
converse). A **3→1 reduction is close**: `relative_entropy_monotone` is already proved (via
physlib DPI) and `support_le_maximally_mixed` already holds; the missing piece is a
generator law. **Action (larger, later):** give `gkls_evolution` a real semigroup/master-
equation defining law, then two of the three axioms fall to lemmas.

---

## C. Pervasive stale documentation — cheap credibility win

**Five+ agents independently flagged this.** Module docstrings and `PROOF_STATUS.md` still
describe already-*proved* theorems as "explicit proof debt" / "proof queue" with axioms
that no longer exist:
- `MaxEntCanonical` docstring; `CoherentFreeEnergy` l.10–13, 266–270;
  `PinchingEntropy` l.1073–1076; `CPTPEmbedding` l.7–15, 45–49; `ClassicalLimit` header;
  `BasicDefinitions` `namespace Axioms` (l.49, containing only proved theorems) + stale
  l.48 comment; `PROOF_STATUS.md` items 3 & 4.
And in the *other* direction, docs **undersell** real results:
- `PhyslibBridge`: A2 strong subadditivity and DPI-monotonicity arrive as fully **proved**
  imports, not "paper-level assumptions" as `axiom-surface.md` states.
- `CoherentFreeEnergy`, `MaxEntCanonical`, `BasicDefinitions`, `MathsAxioms`,
  `ClassicalLimit`: kernel-verified to inherit **none** of the 4 axioms.
**Action:** a documentation-truth pass — make every docstring and `axiom-surface.md` state
the real epistemic status. High credibility value, zero proof risk.

---

## D. Modules confirmed sound (kernel-verified where noted)

| Module | Verdict |
|---|---|
| **BasicDefinitions** | Sound, 0 axioms. Index conventions kernel-pinned by `partial_trace_tensor`. |
| **MathsAxioms** | Clean, 0 axioms, all 7 theorems non-vacuous. (Doc gaps only: `matrix_log` junk contract undocumented; `matrix_log_hermitian` dead `_h` hyp.) |
| **PhyslibBridge** | *Kernel-verified* sound; no sorry leakage despite the pinned physlib having sorries elsewhere. Stronger than docs claim. |
| **CoherentFreeEnergy** | *Kernel-verified* — all 12 theorems inherit none of the 4 axioms. (A4 hypothesis issue is the only defect.) |
| **MaxEntCanonical** | *Kernel-verified* sound; the β>0 Gibbs restatement is honest. Doc-staleness only. |
| **ClassicalLimit** | Sound; `log 0=0` convention verified consistent both sides; 4 former axioms genuinely discharged. |
| **CPTPEmbedding** | No unsound statement; imports axiom-free. (A3 wording issue only.) |
| **PinchingEntropy** | *Kernel-verified* on 7 key theorems (Klein chain, equality case, concavity checked by hand). The 1 axiom is the A2/B1 item. |
| **SQT_Axiom** | *Kernel-verified* consistent; unital restriction faithful to Spohn. The 3 axioms are the B2 item. |
| **Correspondence** | Instances verify what they claim; `corr_consistency` non-circular. (A3 overstatement only.) |
| **InformationTheory** | Capacity/mutual-info are real (no zero/one stubs). **But the Landauer block is A1 — the serious finding.** |

---

## E. Recommended order of work for the next session

1. **A1 — Landauer.** Decide: prove it, or declare it on the axiom surface. This is the one
   that would fail review. (soundness/honesty)
2. **C — documentation-truth pass.** Cheap, high-credibility, zero risk. Fix stale "proof
   debt" language and the under/over-stated axiom claims. Do alongside A1.
3. **B1 — discharge `relative_entropy_jointly_convex`** once PR #1378 merges (cheap; −1
   axiom; closes A2).
4. **A3, A4 — correct the overstated claims / drop redundant hypotheses.** Small edits.
5. **B2 — the SQT_Axiom 3→1 collapse** via a generator defining law. Larger; a real piece
   of formalization, best as its own focused effort.
6. **Legibility (later).** The de-duplication wins (the "sum of eigenvalues = 1" and
   "sum of negMulLog = entropy" bridges are each re-proved ~4× across modules; several
   near-verbatim theorem clones between ClassicalLimit and PinchingEntropy) — real
   tidy-ups for the teaching goal, but after the soundness/honesty items.

Every edit that touches a `.lean` file must pass `cd verification/lean && lake build`
before it is believed. These findings are Fable's analysis; the fixes are yours to make and
verify.
