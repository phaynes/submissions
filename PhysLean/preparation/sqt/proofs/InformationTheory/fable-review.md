# Fable review — `Proofs/InformationTheory.lean` (315 lines, 0 axioms)

Reviewed: 2026-07-08. Build claim (green, 0 sorry/admit) taken from `PROOF_STATUS.md` /
`control/boundary.json`; a grep of the module confirms no `axiom`, `sorry`, `admit`,
`native_decide`, or other escape hatch. Line numbers refer to the module as reviewed.

## 1. What this module proves

The module is a **leaf** of the proof DAG (nothing imports it; it builds via the lakefile
`globs`). It packages two product-corollary stories on top of the entropy core:

- **Classical channels from unitaries.** `ClassicalChannel` (l.18–21: row-stochastic
  `Fin N → Fin N → ℝ`), `unitary_to_channel` (l.25–47: the Born channel `|Uᵢⱼ|²` with a
  real row-normalization proof from `U·Uᴴ = 1`), and two stochasticity statements
  (l.53–68, see §2).
- **Shannon machinery and channel capacity.** `finite_entropy` (l.70–71) bridged to
  `shannon_entropy`/`negMulLog` (l.73–90); the chain-rule inequality
  `finite_entropy_le_joint_of_channel` `H(X,Y) ≥ H(X)` (l.110–176); real definitions of
  `mutual_information` `I = H(X) + H(Y) − H(X,Y)` (l.178–188) and `channel_capacity`
  `= sSup` of achievable mutual informations (l.190–194); and the genuine theorem
  `channel_capacity_bound : channel_capacity ≤ log N` (l.239–257) via
  `I ≤ H(output) ≤ log N`.
- **A Landauer/erasure interface.** `ErasureProcess` (l.263–270) carries the Landauer
  inequality as a **structure field**, and five theorems (l.276–308) restate it; plus a
  trivial `reversible_vs_irreversible` (l.310–313).

Role in the overall argument: terminal corollaries only. No downstream module consumes
these results, so defects here do not propagate — but this module is squarely
reader-facing product surface, so statement honesty matters most here.

## 2. Soundness review

**Headline: nothing false, and the module-specific focus item checks out — the
previously-hidden zero/one stubs for capacity and mutual information are gone.**
`mutual_information` (l.178) is the honest `H(X) + H(Y) − H(X,Y)` over a real
`finite_entropy`; `channel_capacity` (l.190) is an honest `sSup` over all input
distributions. The discharged-axiom ledger confirms `mutual_information`,
`channel_capacity`, and `channel_capacity_bound` were formerly opaque axioms
(TASK-014 rows in `control/axiom-ledger.discharged.ndjson`); they are now real. I checked:

- **The capacity bound is a real proof, correctly junk-guarded.** `channel_capacity_bound`
  (l.239) uses `Real.sSup_le`, whose `0 ≤ a` side condition is discharged honestly,
  including the degenerate `N = 0` case (empty achievable set, `sSup ∅ = 0`, `log 0 = 0`;
  l.253–257). For `N ≥ 1` the achievable set is nonempty and bounded above, so the `sSup`
  is the true supremum — no junk-value vacuity in the statement.
- **The chain-rule inequality is real mathematics.** `finite_entropy_le_joint_of_channel`
  (l.110–176) is `H(X,Y) = H(X) + H(Y|X) ≥ H(X)`, decomposed via `Real.negMulLog_mul` and
  closed with `Real.negMulLog_nonneg` on `0 ≤ Tᵢⱼ ≤ 1` (`channel_transition_le_one`,
  l.101). I verified in the pinned Mathlib that `negMulLog_mul` is **unconditional**
  (`.lake/.../NegMulLog.lean:177` — the junk values `log 0 = 0` make the identity hold at
  zero), so no hidden side condition is being skated over.
- **`finite_entropy`'s zero-guard (l.71) is redundant but consistent** with Mathlib's
  `negMulLog` convention; the agreement lemmas (l.73–90) prove this rather than assume it.
- **`unitary_to_channel` (l.25) is sound**: row normalization genuinely comes from the
  diagonal of `U·Uᴴ = 1`.
- **`von_neumann_entropy` is not a stub** — spectral definition in `PhyslibBridge.lean:21`
  — so the Landauer statements at least reference the real quantity.

Three clusters of **true-but-contentless** statements remain. None is false; all are the
"statement weaker than it looks" pattern the framework history warns about.

1. **`bistochastic_preserves_uniform` (l.58–68) is trivially true for *every* channel and
   does not state stationarity of the uniform distribution.** The module's convention
   (from `normalized`, l.21) is that the **first** index is the input, so forward
   evolution of a distribution is `out(j) = ∑ᵢ π(i)·T(i,j)`. The theorem instead proves
   `∑ᵢ T(j,i)·π(i) = π(j)` — a sum along **row** `j`, which for uniform `π` is
   `(1/N)·(row sum) = 1/N` for **any** row-stochastic channel. The unitarity of `U` is
   used only to construct the channel; a verbatim proof goes through for an arbitrary
   `ClassicalChannel`. The genuine physics (the classical shadow of unitality: uniform is
   stationary because `|Uᵢⱼ|²` is doubly stochastic) requires **column** sums
   `∑ᵢ T(i,j) = 1`, which is exactly what `unitary_channel_bistochastic` (l.53–56) does
   *not* prove — its own docstring (l.49–52) honestly flags that it merely re-asserts the
   `normalized` field. Credit for that flag; but the downstream
   `bistochastic_preserves_uniform` carries **no** flag and a name that claims the
   unproved content. This is the module's one substantive mathematical gap.

2. **The Landauer block (l.263–308) assumes its own conclusion by construction.**
   `ErasureProcess.heat_landauer_bound` (l.270) makes the Landauer inequality a structure
   **field**; every theorem in the block is then a projection or a rewrite of it:
   - `landauer_bound` (l.276) and `landauer_principle` (l.280) unpack the field.
   - `landauer_qubit_erasure` (l.286) and `maxwell_demon_resolution` (l.302) take
     hypothesis `h_Q : Q ≥ (1/β)·S(ρ)` and conclude **the same inequality** — hypothesis
     literally equals conclusion modulo the `let`-binding.
   - `landauer_maximal_entropy_bit` (l.294) adds only the rewrite `S(ρ) = log 2`.

   The publication writeup is honest about this ("The erasure process carries a heat
   field and an explicit model assumption… The Landauer bound follows from that model
   field", `docs/publication/sqt-conditional-proof-writeup.md:175–191`), and the module
   docstring (l.9–11) declares the bounds proof debt. **But**: (a) the theorem names —
   especially `maxwell_demon_resolution` — read as results and will draw referee fire;
   (b) unlike `unitary_channel_bistochastic`, none of these declarations carries an
   in-code flag; and (c) most importantly, **this assumption is invisible to the 4-axiom
   headline**. The axiom surface is counted by `axiom` declarations; an
   assumption-carrying structure field evades that count. `axiom-surface.md` lists A1/A2/A4
   as interface/bridge assumptions but does not mention `heat_landauer_bound`. It should.
   Corroborating evidence that no derivation exists: the `final` / `final_is_pure` fields
   (l.265–266) are **never used by any theorem** — in a real Landauer proof
   `ΔS = S(init) − S(final)` needs them.

3. **`reversible_vs_irreversible` (l.310–313) proves `S(ρ) = S(ρ)` by `rfl`.** The
   `U.unitary` fact is bound to `_` purely as decoration. The intended content — unitary
   invariance `S(UρU†) = S(ρ)` — is absent from the framework (and is, notably, an
   ingredient the real Landauer derivation would need). Delete or upgrade.

Minor statement-hygiene notes (not soundness): `landauer_principle`'s `h_T_pos` (l.281)
is redundant given `h_T_def` and `beta_pos`, and is consumed only by a `have _ :=`
(l.283); `erasure_heat`'s `H : Hermitian n` argument (l.272–274) is decorative and infects
every Landauer statement with an unused parameter.

I checked and found sound: the upstream `shannon_entropy_le_log` this module leans on
(l.99) is a real Jensen argument via `Real.concaveOn_negMulLog`
(`ClassicalLimit.lean:147`), not residual debt, despite `PROOF_STATUS.md`'s stale-looking
"Shannon upper bound" priority item.

## 3. Axiom-reduction opportunities

The module has 0 axioms; the tightening targets are the implicit assumptions above.

1. **Discharge `heat_landauer_bound` into a theorem (the real prize).** Concrete path, in
   the Reeb–Wolf style (NJP 16, 103011 (2014)): model erasure as a unitary on
   system ⊗ bath with the bath initially Gibbs at `β`; then
   `β·Q ≥ S(init) − S(final)` follows from (i) unitary invariance of `S` (missing — the
   honest replacement for `reversible_vs_irreversible`; provable spectrally, since
   eigenvalues are conjugation-invariant), (ii) subadditivity of `S` (in the
   `PinchingEntropy` multipartite bridge, per the proof map), (iii) the Gibbs
   relative-entropy identity (`MaxEntCanonical` / PROOF_STATUS priority 4), and (iv)
   nonnegativity or monotonicity of relative entropy — note `PhyslibBridge` already
   imports `QuantumInfo.Entropy.DPI` and `.SSA` from physlib, so the heavy analysis can
   come from upstream rather than this dev. Most ingredients exist in-tree; the genuinely
   new pieces are unitary invariance of `S` and the bath-coupling model. Until then, the
   cheap honest fix is to list `ErasureProcess.heat_landauer_bound` alongside A1/A2/A4 in
   `axiom-surface.md` as a named interface assumption.
2. **Prove true double stochasticity.** `∑ᵢ |Uᵢⱼ|² = 1` needs `Uᴴ·U = 1`, obtainable from
   the existing `U.unitary : U·Uᴴ = 1` field via the square-matrix fact
   `mul_eq_one_comm` (present in the pinned Mathlib; `Matrix.mul_eq_one_comm` survives as
   a deprecated alias, `SemiringInverse.lean:235`). Then restate
   `bistochastic_preserves_uniform` in the forward direction
   `∑ᵢ π(i)·T(i,j) = π(j)`. Small, self-contained, and it discharges the framework
   weakness flagged at l.49–52.
3. **`mutual_information ≥ 0` / capacity lower bound.** Only the upper bound is proved;
   `I ≥ 0` needs subadditivity `H(X,Y) ≤ H(X) + H(Y)`, provable with the same
   `concaveOn_negMulLog` Jensen machinery already deployed in
   `ClassicalLimit.shannon_entropy_le_log`. This would pin `channel_capacity ∈ [0, log N]`
   and make the `sSup` provably a max over a nonempty set rather than relying on the
   reader to see it.

## 4. Legibility / teaching notes

1. **`finite_entropy_le_joint_of_channel` (l.110–176) is the hardest read** — a 40-line
   inline `calc` (`hdecomp`, l.129–165) hiding the chain rule. For teaching, extract two
   named lemmas: a chain-rule *equality* `H(joint) = H(input) + H_cond` and
   `0 ≤ H_cond`, with a named `conditional_entropy` definition. The chain rule is the
   pedagogical point; right now it is anonymous plumbing inside an inequality.
2. **`mutual_information` carries two proof arguments it ignores** (`let _ :=`,
   l.182–183). Take a `ProbDist N` (already defined, `ClassicalLimit.lean:24`) instead of
   the `(dist, nonneg, norm)` triple. This also collapses `channel_capacity`'s
   triple-nested existential (l.191–194) to `∃ p : ProbDist N`, and unifies the API with
   `shannon_entropy`.
3. **The Landauer block needs its dishonesty made local.** Whatever the discharge
   timeline, each declaration should carry the same style of in-code flag as l.49–52
   ("restates the model field; not a derivation"), the decorative `H` and redundant
   `h_T_pos` arguments should go, and `maxwell_demon_resolution` should be renamed to
   what it is (an erasure-cost interface instance). The `let proc := …` bindings inside
   theorem *statements* (l.290, 298, 306) make the conclusions awkward to read and to
   apply; phrase conclusions directly.
4. **The module docstring (l.9–11) is stale**: "Hard information-theoretic bounds are
   explicit proof debt" undersells the now-proved capacity bound and doesn't name the one
   thing that *is* still assumed (Landauer via the structure field). Say precisely that.

## 5. Verdict

The capacity half of this module is in genuinely good shape — real definitions where
stubs once were, a real chain-rule proof, and a correctly junk-guarded `sSup` bound; I
found no false statement anywhere in the file. The residual problems are honesty-of-
packaging, concentrated in three places: the Landauer block assumes its conclusion via a
structure field that the 4-axiom headline cannot see, `bistochastic_preserves_uniform`
proves a triviality under a physics-claiming name, and `reversible_vs_irreversible` is
`rfl`. Ranked follow-ups: **(1)** declare `heat_landauer_bound` in `axiom-surface.md` as
a named interface assumption and flag/rename the tautological Landauer theorems
(soundness-of-claims; do first, cheap); **(2)** prove column stochasticity via
`mul_eq_one_comm` and restate uniform stationarity in the forward direction (small real
math; closes the flagged weakness); **(3)** legibility pass — `ProbDist` refactor of
MI/capacity, chain-rule lemma extraction, and delete-or-upgrade
`reversible_vs_irreversible` (ideally upgraded to `S(UρU†) = S(ρ)` as the first brick of
a future Reeb–Wolf Landauer derivation).
