# Fable review — `Proofs/MathsAxioms.lean`

**Reviewed:** 2026-07-08 · 99 lines · 0 axioms, 0 sorries (grep-verified; consistent with
`control/boundary.json`, which lists no per-module entry for this file).
**Scope:** analysis only; no source edits. Claims about Mathlib behavior below were checked
against the pinned Mathlib in `.lake/packages/mathlib` (not from memory).

## 1. What this module proves

This is the root of the proof DAG (no `Proofs.*` imports). Despite the legacy name it now
contains **zero axioms**; every declaration is a real definition or a proved theorem. It
supplies the two load-bearing objects of the entire development plus small supporting facts:

- **`matrix_log`** (line 22): the matrix logarithm, defined as `cfc Real.log M` via Mathlib's
  continuous functional calculus. This underlies every entropy quantity downstream
  (`von_neumann_entropy`, relative entropy, free energy — see `PinchingEntropy.lean:315ff`,
  `CoherentFreeEnergy.lean:204ff`).
- **`partialTrace₂`** (lines 61–64): a fully concrete partial trace over the second tensor
  factor — an explicit entry-level sum `∑ k, ρ (finProdFinEquiv (i,k)) (finProdFinEquiv (j,k))`
  — with proved conjugate-transpose commutation (67–72), PSD preservation (75–87), and trace
  preservation (90–99). This underlies all marginals, and hence SSA/Araki–Lieb, downstream.
- Supporting lemmas: `matrix_log_hermitian` (26), trace cyclicity `trace_mul_matrix_log` (32),
  trace additivity `trace_mul_log_linear` (37), `kronecker_posSemidef` (45, a wrapper over
  Mathlib's `Matrix.PosSemidef.kronecker`), and `trace_reindex` (51, via `Equiv.sum_comp`).

## 2. Soundness review

**Headline: nothing unsound found.** What I checked, and the two wrinkles worth recording:

1. **Axiom-free status confirmed.** No `axiom`, `sorry`, or `admit` in the file.

2. **`matrix_log` junk-value contract (line 22) — a convention, not a defect, but it is THE
   semantic contract of the file.** In the pinned Mathlib, `cfc f a` returns the junk value
   `0` when the predicate fails or `f` is not continuous on the spectrum
   (`ContinuousFunctionalCalculus/Unital.lean:307`). For finite matrices the spectrum is
   finite, so the continuity branch is automatic; the junk triggers are exactly:
   - **non-hermitian `M`** → `matrix_log M = 0`;
   - **hermitian `M` with zero eigenvalues** → `Real.log 0 = 0` applied spectrally;
   - **hermitian `M` with negative eigenvalues** → `Real.log` is even
     (`Real.log_neg_eq_log`, Mathlib `Log/Basic.lean:120`), i.e. `log |λ|`.

   The definition makes no PSD or invertibility demand; all safety is downstream discipline.
   The development demonstrably exercises that discipline — the comment at
   `PinchingEntropy.lean:319` records the axiom refuted *precisely because* "`matrix_log`
   uses `Real.log 0 = 0`", and the surviving joint-convexity axiom is rescoped on-support.
   No theorem *in this module* is weakened by the convention: all seven theorems state real,
   non-vacuous properties that hold for the junk-total function.

3. **`matrix_log_hermitian` (lines 26–29): the hypothesis `_h : M.conjTranspose = M` is
   dead.** The proof term `cfc_predicate Real.log M` is unconditional in the pinned Mathlib
   (`cfc_predicate (f : R → R) (a : A) : p (cfc f a)`, `Unital.lean:405` — it covers the junk
   branch via `p 0`). So the theorem is true *a fortiori* — the statement is actually
   **stronger than it looks**, not weaker; hermiticity of the output needs no assumption on
   the input in this encoding. Not a soundness problem, but the vestigial hypothesis misleads
   a reader into thinking input-hermiticity is doing work. Drop it, or keep it with a comment
   explaining why it is unnecessary (a good junk-value teaching moment).

4. **`partialTrace₂` factor convention — verified downstream, because it cannot be verified
   here.** The three properties proved in this module (hermiticity, PSD, trace preservation)
   are symmetric between the two factors: they would hold identically for a partial trace over
   the *first* factor, so nothing in-module pins down that "₂" means the second subsystem.
   I checked that the convention is kernel-pinned downstream, three independent ways:
   - `partial_trace_tensor` (`CPTPEmbedding.lean:248–273`):
     `partial_trace (tensor_product ρ τ) = ρ` — tracing out the second factor recovers the
     first, with `tensor_product` built from `Matrix.kronecker` reindexed by the same
     `finProdFinEquiv` (`BasicDefinitions.lean:98–103`).
   - `toMStatePair_traceRight` (`PhyslibBridge.lean:154–162`): `partialTrace₂` agrees with
     the external physics library's `MState.traceRight` under the same relabeling (and
     `toMStatePair_traceLeft` mirrors this for `partialTrace₁`).
   - The pinned Mathlib `finProdFinEquiv (i,k) = k + n·i` (`Equiv/Fin/Basic.lean:329–331`):
     first factor coarse (block index), second factor fine — the standard row-major Kronecker
     layout, so summing `k` is genuinely the second-subsystem trace.

   Conclusion: consistent throughout; no swapped-convention hazard.

5. **`partialTrace₂_pos` (75–87)** is a real proof: the decomposition into a sum of
   same-index compressions `ρ.submatrix (fun i => finProdFinEquiv (i,k)) …` is correct, and
   `Matrix.PosSemidef.submatrix` legitimately applies to the (injective, non-surjective)
   compression maps. **`trace_partialTrace₂` (90–99)** is the honest reindexed diagonal sum.
   Neither hides an assumption.

6. **No definition pre-assumes a downstream obligation.** `partialTrace₂` is concrete (not an
   opaque constant), and `matrix_log` delegates to Mathlib's standard `cfc` encoding.

## 3. Axiom-reduction opportunities

None in-module (0 axioms). Implicit-assumption tightening worth doing:

- **Make the junk contract explicit at the source.** The one remaining entropy axiom
  (`relative_entropy_jointly_convex`, on-support, `PinchingEntropy.lean`) exists *because of*
  `matrix_log`'s `log 0 = 0` convention. A docstring on `matrix_log` stating the three junk
  behaviors in §2.2 above would move the framework's hardest-won lesson to where every reader
  first meets the definition.
- **Centralize the spectral unfolding.** Both `PinchingEntropy.lean:354` and
  `CoherentFreeEnergy.lean:214` re-derive `matrix_log M = hM.cfc Real.log` via
  `Matrix.IsHermitian.cfc_eq` inline. A named lemma here (e.g.
  `matrix_log_eq_spectral (hM : M.IsHermitian) : matrix_log M = hM.cfc Real.log`) would
  de-duplicate the two call sites and give the teaching reader the eigendecomposition
  semantics as a stated fact rather than a tactic step.
- **Wrapper retirement (low priority).** `trace_mul_matrix_log`, `trace_mul_log_linear`, and
  `kronecker_posSemidef` are one-line restatements of `Matrix.trace_mul_comm`,
  `mul_add`+`trace_add`, and `Matrix.PosSemidef.kronecker`, kept to preserve old axiom-era
  call sites. They could be inlined away or marked as compatibility shims. `trace_reindex`
  earns its keep: I found no equivalent trace-under-`reindex` lemma in the pinned Mathlib.
- **Long-run dedup with PhysLean:** once the physlib bridge is the primary entropy carrier,
  `matrix_log` itself could in principle be retired in favor of the upstream functional
  calculus, shrinking this file's trusted-definition surface to zero. That is a refactor,
  not an axiom discharge; nothing here blocks the planned `qRelativeEnt_joint_convexity`
  discharge (PhysLean PR #1378 path per `axiom-surface.md`).

## 4. Legibility / teaching notes

1. **The module name and docstring are now actively misleading — the top fix.** A reviewer
   opens the DAG root named `MathsAxioms` whose header (lines 8–13) says "Matrix-level
   placeholders for missing functional calculus" and forms exactly the wrong prior; the file
   contains zero axioms and zero placeholders. Rename (e.g. `MatrixFacts`, or split
   `MatrixLog` + `PartialTrace`) or rewrite the header to state (a) what the file now
   provides, and (b) the two conventions the reader must carry through the whole development:
   the junk `cfc`/`Real.log 0 = 0` contract, and the `finProdFinEquiv` row-major pairing with
   factor 1 coarse.
2. **Strip internal provenance from teaching-facing source.** "Discharged (was an axiom)"
   framing (lines 20, 31, 36, 44, 66, 73, 89) and especially "Proof attempt by Codex GPT-5.5
   (140s)" (line 21) are ledger/git-history material, not review material. Keep the genuine
   mathematical insight sentences — the `partialTrace₂_pos` docstring ("a SUM of same-index
   submatrix compressions … PSD is closed under sum", lines 73–74) is exactly the right kind
   of comment.
3. **Drop the unused `_h` in `matrix_log_hermitian`** (or annotate why it is unnecessary).
4. **Point the reader at the convention witness.** A one-line forward reference on
   `partialTrace₂` to `partial_trace_tensor` (CPTPEmbedding) and `toMStatePair_traceRight`
   (PhyslibBridge) tells the reader immediately *which* factor dies and where that claim is
   kernel-checked — the in-module theorems alone cannot show it (§2.4).

## 5. Verdict

This module is genuinely clean: axiom-free, all seven theorems non-vacuous and honestly
stated, the partial-trace convention consistent and kernel-pinned downstream, and the one
junk-value contract (`matrix_log`) already respected by the rest of the development. The
residual work is reader-facing, not mathematical. Ranked follow-ups: **(1)** remove or
justify the dead hypothesis in `matrix_log_hermitian` (lines 26–29) — the only statement
whose surface form misrepresents its logical content (cheap, do first); **(2)** rename the
module and rewrite the header docstring, stating the `matrix_log` junk contract and the
`finProdFinEquiv` convention up front — the highest-value legibility fix before external
review, since this is the first file a PhysLean reviewer reads; **(3)** extract
`matrix_log_eq_spectral` to de-duplicate the `IsHermitian.cfc_eq` unfolding repeated in
`PinchingEntropy.lean:354` and `CoherentFreeEnergy.lean:214` (polish, do later).
