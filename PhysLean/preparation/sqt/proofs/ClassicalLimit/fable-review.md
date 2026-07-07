# Fable review — `Proofs/ClassicalLimit.lean`

**Module:** `verification/lean/Proofs/ClassicalLimit.lean` (264 lines, 0 axioms, 0 sorries)
**Reviewer:** Fable 5 (analysis only; no source edited)
**Focus:** classical embedding agreement — probability embedding, entropy agreement, Shannon bound, expectation agreement.

---

## 1. What this module proves

The module realizes the classical limit as a *diagonal embedding* of finite probability
distributions into the quantum formalism, and proves the embedding is faithful for entropy
and expectation values:

- `ProbDist n` (line 24) — honest finite distribution: `prob : Fin n → ℝ`, `nonneg`, `sum_one`.
- `embed_prob` (line 45) — `p ↦ diagonal (p.prob · : ℂ)` as a `DensityMatrix n`, with all
  three well-formedness fields (Hermitian, PSD, trace 1) genuinely proved.
- `entropy_agreement` (line 74) — **the centerpiece**: `von_neumann_entropy (embed_prob p) =
  shannon_entropy p`. Proved spectrally: charpoly of the diagonal matrix
  (`Matrix.charpoly_diagonal`) vs. charpoly roots = eigenvalue multiset
  (Mathlib `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`), injectivity of `ℝ → ℂ` to
  descend to a real multiset equality, then permutation-invariance of the `negMulLog` sum.
- `shannon_entropy_nonneg` (136), `shannon_entropy_le_log` (147) — `0 ≤ H(p) ≤ log n`, the
  latter by Jensen for the concave `Real.negMulLog` with uniform weights.
- Tightness witnesses at both ends: `uniform_entropy_eq_log` (203) and
  `deterministic_entropy_zero` (219) — valuable non-vacuity evidence.
- `expectation_agreement` (245) — `Re tr(diag(p)·diag(vals)) = ∑ pᵢ valsᵢ`.
- `is_classical` (251), `classical_state_entropy` (254), `quantum_generalizes_classical`
  (260) — packaging corollaries.

Role in the DAG: leaf-ward module over `PinchingEntropy`; its only downstream consumer is
`InformationTheory`, which uses `ProbDist`/`shannon_entropy`/`shannon_entropy_le_log` for the
channel-capacity bound (`finite_entropy_le_log_of_dist`, InformationTheory.lean:92–99). The
agreement theorems themselves are terminal deliverables of the SQC classical-limit claim.

## 2. Soundness review

**I found no soundness defect.** What I checked, specifically:

- **Junk-value artifacts.** `shannon_entropy` uses bare `p * log p` (no guard);
  `von_neumann_entropy` (PhyslibBridge.lean:21) uses an `if λ = 0` guard. Both coincide with
  `Real.negMulLog` because Mathlib's `log 0 = 0` junk value *equals* the correct analytic
  limit `x log x → 0` here — the convention is consistent on both sides of
  `entropy_agreement`, so nothing is trivialized. `Real.negMulLog_mul` (used at line 178) is
  genuinely unconditional in Mathlib (verified in the vendored source,
  `NegMulLog.lean:177`) — its use without positivity side-conditions is correct, not a gap.
  `uniform_dist`'s `1/n` never hits `1/0` (guarded by `hn : n > 0`).
- **Vacuity.** `ProbDist 0` is uninhabited (`sum_one` fails over the empty type), so `∀ p`
  statements are vacuous at `n = 0` — inherent and unexploited. Notably
  `shannon_entropy_le_log` *derives* `n ≠ 0` from `p.sum_one` (lines 149–153) rather than
  hypothesizing it, and the uniform/deterministic witnesses inhabit the interface for every
  `n > 0` and pin both ends of the bound. No vacuous-hypothesis tricks anywhere.
- **Stub definitions.** None. `von_neumann_entropy` is the real spectral quantity
  (Mathlib `IsHermitian.eigenvalues`), further anchored externally by
  `entropy_toMState` (PhyslibBridge.lean:129) equating it with physlib's `Sᵥₙ`. The
  eigenvalue-multiset argument in `entropy_agreement` (lines 77–107) matches the semantics of
  the Mathlib lemmas it invokes (I verified `roots_charpoly_eq_eigenvalues` in the vendored
  `Mathlib/Analysis/Matrix/Spectrum.lean:159` states exactly the multiset form used).
- **Silent truncation.** `expectation_value_quantum` takes `.re` of `tr(ρO)` (line 238). For
  Hermitian `ρ, O` the trace is provably real, so `.re` is faithful; and in
  `expectation_agreement` both matrices are real diagonals, so no imaginary part is being
  discarded. (An explicit `(tr(ρ.matrix * O.matrix)).im = 0` lemma would make this
  self-certifying — see §3.)
- **Definitions assuming downstream conclusions.** None. One honest-statement nuance to keep
  in the prose: `is_classical` (line 251) means "diagonal *in the computational basis*"
  (basis-relative), via `DensityMatrix.matrix_ext` proof-irrelevance. That is the right
  notion for the embedding-agreement argument, but a physics reviewer may read "classical
  state" as basis-independent; the docstring should say so.

Two statement-level observations that are not unsoundness but affect how much is claimed:

1. `quantum_generalizes_classical` (line 260) is a verbatim re-export of `entropy_agreement`
   under a much grander name. Nothing false — but the name promises structural
   generalization (dynamics, observables, everything), while the content is one entropy
   equation. Rename or delete (see §4).
2. `classical_state_entropy`'s existential does not assert uniqueness of `p`; it is in fact
   unique (diagonal entries recover `p`), but that is unproved. Not wrong — just weaker than
   the module could easily state.

## 3. Axiom-reduction opportunities

The module has **0 axioms**, and the ledger confirms its four former axioms (`embed_prob`,
`entropy_agreement`, `shannon_entropy_le_log`, `expectation_agreement`;
`axiom-ledger.discharged.ndjson` rows 24–27) are all discharged to real constructions/proofs.
Nothing here needs an axiom. Implicit-assumption tightenings, in value order:

- **`embed_prob` injectivity** (`embed_prob p = embed_prob q → p = q`): one diagonal-entry
  argument plus `ProbDist` extensionality. Upgrades "classical states embed" to "embed
  *faithfully*", and gives uniqueness in `classical_state_entropy` for free. Pure Mathlib
  (`Matrix.diagonal` injectivity + `Complex.ofReal_injective`).
- **Reality of the expectation pairing**: `(tr(ρ.matrix * O.matrix)).im = 0` for
  `ρ : DensityMatrix n`, `O : Hermitian n` — makes the `.re` in
  `expectation_value_quantum` visibly lossless. Short conjTranspose/trace-cyclicity argument.
- Note: Mathlib has **no** ready-made finite Shannon bound (`InformationTheory/` has only
  Coding/Hamming/KullbackLeibler; nothing in `NegMulLog.lean`), so `shannon_entropy_le_log`
  is doing real work not replaceable by an import — though it *is* replaceable by results
  already in this development (see §4, item 1).

## 4. Legibility / teaching notes

Ranked; describe-only, no code.

1. **The Jensen proof is a near-verbatim clone of `PinchingEntropy.entropy_max_at_mixed`.**
   `shannon_entropy_le_log` (lines 147–191) reproduces, step for step, the weighted-Jensen
   scaffold of `entropy_max_at_mixed` (PinchingEntropy.lean:53–110) with `ρ.eigenvalues`
   replaced by `p.prob`. Two clean options: (a) *derive* it in two steps —
   `shannon_entropy p = von_neumann_entropy (embed_prob p) ≤ log n` via `entropy_agreement`
   and `entropy_max_at_mixed`, which doubles as a teaching moment ("the classical bound is
   the quantum bound restricted along the embedding"); or (b) if a self-contained classical
   proof is preferred pedagogically, extract the shared Jensen core ("for weights 1/n and
   nonneg points summing to 1, `∑ negMulLog xᵢ ≤ log n`") into one lemma both modules use.
   Current state — two 45-line clones — is the worst of both.
2. **The `∑ negMulLog = entropy` bridge is proved at least four times.** Inside this module
   twice (`hentropy_classical` at 128–133 vs `hentropy_eq` at 182–186 — the *same fact* in
   the *same file*), once as `hentropy_quantum` (119–127, duplicating
   PinchingEntropy.lean:59–65), and again as
   `InformationTheory.finite_entropy_eq_sum_negMulLog` (73–81). Name them once —
   `shannon_entropy_eq_sum_negMulLog` and `von_neumann_entropy_eq_sum_negMulLog` — and every
   entropy proof in the development gets shorter and more citable.
3. **Extract the diagonal-spectrum lemma from `entropy_agreement`.** Lines 77–107 (the chain
   `hcp → hroots_diag → hroots_eig → hmap_eq → hmset_eq → hmset_eq'`) prove a reusable fact:
   *the eigenvalue multiset of `diagonal (ofReal ∘ f)` is the multiset of `f`*. As a named
   lemma the main theorem becomes three legible steps (spectrum of the embedding = the
   distribution; `negMulLog` sums are multiset-invariant; both entropies are `negMulLog`
   sums). The `congr 1` at line 97 rests on a definitional-equality coincidence
   (`fun i => (p.prob i : ℂ)` vs `RCLike.ofReal ∘ p.prob`) — fine for the kernel, opaque for
   a reader; stating one composed form removes it.
4. **Stale header and provenance noise — fix before submission.** The module docstring
   (lines 11–15) still says the file "exposes the remaining mathematical work as explicit
   proof debt" — false since the discharge wave: there is none (0 axioms, 0 sorries). A
   PhysLean reviewer told to hunt for proof debt and finding none will be confused, not
   impressed. Likewise PROOF_STATUS.md's priority item 1 ("Classical limit: prove …") lists
   exactly the four already-discharged items. The model-attribution docstrings
   ("Discharged … by Codex GPT-5.5 (96s)", lines 43, 71, 145, 244) belong in the ledger, not
   in rendered doc comments of a submission artifact.
5. **Naming/duplication smalls.** The two identical 12-line Hermitian-by-cases proofs in
   `embed_prob` (47–55) and `embed_observable` (226–234) are one `simp` away via Mathlib's
   `Matrix.isHermitian_diagonal_iff` (verified present in the vendored Mathlib,
   `Hermitian.lean:178`), or one shared local lemma. Rename or drop
   `quantum_generalizes_classical`; document `is_classical`'s basis-relativity.

## 5. Verdict

This module is **sound and in good shape** — the strongest kind of clean: real spectral
content (no stubs), junk-value conventions verified consistent on both sides of every
equation, non-vacuity witnessed at both extremes of the entropy bound, and 0 axioms with all
four former axioms genuinely discharged. There are no soundness fixes to make. The
highest-value follow-ups, ranked: **(1)** fix the stale module header and the stale
PROOF_STATUS priority item and relocate model-attribution comments — cheap, and directly
protects credibility with an external PhysLean reviewer (do first); **(2)** deduplicate the
Jensen scaffold and the `negMulLog` bridges (§4.1–4.2) — the single biggest legibility win,
and it converts `shannon_entropy_le_log` into a two-line corollary that *teaches* the
embedding story; **(3)** add the two small interface strengtheners (`embed_prob`
injectivity, `im = 0` for the expectation pairing) so the `.re` and the existential in
`classical_state_entropy` are visibly lossless. (1) is documentation, (2)–(3) are polish;
none blocks the conditional-proof claim.
