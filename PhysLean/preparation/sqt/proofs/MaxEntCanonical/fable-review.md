# Fable review — `MaxEntCanonical.lean`

**Module:** `verification/lean/Proofs/MaxEntCanonical.lean` (149 lines, 0 axioms, 0 sorry/admit)
**Reviewed:** 2026-07-08. Analysis only; no source edits. Kernel checks run via a scratch file with `lake env lean`.

## 1. What this module proves

A **leaf module** (nothing imports it — confirmed by grep) sitting on top of `CoherentFreeEnergy`; it is the terminal product corollary of the thermodynamics layer. Four theorems:

- `canonical_unique_max_entropy` (l.33) — **fixed-β Jaynes principle with uniqueness**: for `β > 0`, among all density matrices with the same energy as the canonical state `γ = canonical_state H β`, either `ρ = γ` or `S(ρ) < S(γ)`. This is exactly the corrected form promised when the false axiom `max_entropy_at_fixed_energy` (arbitrary-`E` existential) was deleted; `CoherentFreeEnergy.lean` l.266–270 still calls it "a future loop target", but it is delivered here.
- `canonical_unique_min_free_energy` (l.66) — strict-uniqueness upgrade of the Gibbs variational principle (`canonical_minimizes_free_energy` in CFE gives only `≤`): `ρ ≠ γ → F(γ) < F(ρ)`.
- `canonical_commutes_with_hamiltonian` (l.91) — `[γ, H] = 0` for every `β`, by spectral decomposition in `H`'s own eigenbasis.
- `partition_function_free_energy_relation` (l.140) — `log Z = −β F(γ)` for `β > 0`.

**Kernel-verified axiom cone:** `#print axioms` on all four theorems (and on the imported load-bearing lemmas `relative_entropy_gibbs_identity`, `relative_entropy_real_nonneg_of_support`, `relative_entropy_eq_zero_iff`, `support_le_canonical`, `canonical_state`) reports only `[propext, Classical.choice, Quot.sound]`. **None of the project's 4 axioms enters this module's dependency cone** — the canonical-thermodynamics story here is unconditional modulo Lean's standard classical axioms. In particular it does not even use the on-support joint-convexity axiom.

## 2. Soundness review

**Result: no unsoundness found.** What was checked, and the one metadata-level defect:

**The Gibbs relative-entropy identity restatement (module focus).** `relative_entropy_gibbs_identity` (CFE l.436): `D(ρ‖γ_β) = β(F(ρ) − F(γ_β))` under `h_β : β > 0`. Verified sound on three fronts:

1. *The quantities are honest.* `canonical_state` (CFE l.90–146) is a real spectral Gibbs construction `V·diag(e^{−βμᵢ}/Z)·V†` with proved PosDef, Hermitian, trace-1 — not a stub. `free_energy` is the genuine `Re Tr(ρH) − (1/β)S(ρ)`; taking `.re` of `Tr(ρH)` loses nothing for Hermitian pairs.
2. *The junk convention cannot engage.* `relative_entropy_real ρ σ = Re Tr(ρ(log ρ − log σ))` is honest only on-support, but `γ_β` is PosDef (all Gibbs weights strictly positive), so `log γ` never touches `Real.log 0 = 0`; on the `ρ` side, zero eigenvalues of `ρ` multiply their own junk `log 0` terms to zero, matching the if-guarded `von_neumann_entropy` (PhyslibBridge l.21) — this is precisely `trace_self_log_eq_neg_entropy`. So for *every* `ρ`, `relative_entropy_real ρ (canonical_state H β)` is the true quantum relative entropy, and the identity is the textbook one, not a junk-value coincidence.
3. *The guard is honest and necessary in the right direction.* At `β = 0` Lean's `1/0 = 0` makes `free_energy` drop its entropy term; the unguarded identity would claim `log n − S(ρ) = 0` — genuinely false, which is why it was restated. Guards only restrict, so no unsoundness. One scope note: the identity (and `partition_function_free_energy_relation`) actually holds for all `β ≠ 0` — the proofs use only `β ≠ 0` (`h_β.ne'`) plus `canonical_entropy_eq`, which is unconditional in `β`. `β > 0` is therefore slightly stronger than mathematically necessary for those two, though it is the physically standard scope and **is** essential for `canonical_unique_min_free_energy` (at `β < 0` the canonical state *maximizes* free energy).

**The uniqueness route.** Both uniqueness theorems (l.45–58 and l.73–86) hinge on: `support_le ρ γ` always holds (`support_le_canonical`, CFE l.155 — honest trivial-kernel argument from PosDef, no hidden assumption), Klein nonnegativity (`relative_entropy_real_nonneg_of_support`, PinchingEntropy l.1077), and the Klein equality case (`relative_entropy_eq_zero_iff`, PinchingEntropy l.1410). Both are **proved theorems** (diagonalization + doubly-stochastic overlap + Jensen), not axioms — kernel-confirmed. `ρ = σ` there is full `DensityMatrix` equality via proof-irrelevant `matrix_ext` (BasicDefinitions l.33), so the disjunction in `canonical_unique_max_entropy` is not weakened by a shallow equality notion.

**Vacuity checks.** `canonical_unique_max_entropy`'s `h_energy` pins `E` to `γ_β`'s own energy — satisfiable for every `H, β` (take `E := Tr(γH).re`), and the correct fixed-β Jaynes form (the arbitrary-`E` version is the refuted deleted axiom). `[NeZero n]` is required for `Z > 0`; honest. `canonical_commutes_with_hamiltonian` is unconditional in `β` and its `change` at l.101 was checked to be defeq to the actual `canonical_matrix`/`canonical_weight` construction. No `True`-shaped goals, no zero/one stubs, no dead hypotheses.

**The one defect found (metadata, not proof):** the **module docstring is false** (l.3–9): "these statements are now explicit proof debt." The module contains complete proofs and zero axioms. For a package headed to external review, a header that misdeclares the epistemic state of its own contents is an honesty bug even though no theorem is affected. The same staleness pattern appears in the module's neighbourhood: CFE header l.10–13 ("the difficult analytic and variational facts are explicit axioms" — CFE has 0), CFE l.266–270 ("future loop target" — met here), the "Kept as an EXPLICITLY SCOPED axiom" docstring on the now-proved `relative_entropy_real_nonneg_of_support` (PinchingEntropy l.1073–1076), and PROOF_STATUS.md priority 4 ("construct the Gibbs state and prove the Gibbs relative-entropy identity" — both done).

## 3. Axiom-reduction opportunities

None needed: the module has no axioms and, kernel-verified, imports none of the project's 4. Two tightening options, both optional:

- Relax `β > 0` to `β ≠ 0` on `relative_entropy_gibbs_identity` and `partition_function_free_energy_relation` (drop-in: only `.ne'` is used). `canonical_unique_max_entropy` is also *true* for `β ≠ 0` (negative-temperature Jaynes), but its current proof uses the sign of `β` twice; extending would need a sign-case split — do not bother for the PhysLean submission unless negative temperatures are in scope.
- Advertise the unconditional status: the axiom-surface/proof-map docs say "no axioms" for this module, but the stronger, checkable statement — the entire canonical-thermodynamics corollary layer depends only on `propext, Classical.choice, Quot.sound` — is worth stating explicitly (e.g. a `#print axioms` line in-file, as `CoherentFreeEnergy` already does for its witnesses at l.380–381).

## 4. Legibility / teaching notes

Ranked by value for a reviewer reading this as a step-by-step argument:

1. **Fix the module docstring** (l.3–9) to say what the module now is: four proved, axiom-clean canonical-ensemble results, with one line each. Highest value per character of any change available here.
2. **Deduplicate the two uniqueness proofs.** Lines 45–58 and 73–86 are the same eight-step block (`support_le` → Klein `≥ 0` → `≠ 0` via equality case → `D > 0` → Gibbs identity → `F`-gap `> 0`). Extract one named lemma (e.g. "for `ρ ≠ γ_β` the free-energy gap is strictly positive") or, better for the narrative, reorder so `canonical_unique_min_free_energy` comes first and `canonical_unique_max_entropy` is visibly its corollary (equal energies convert the `F`-gap into an entropy gap). That ordering — variational principle, then Jaynes — is also the standard physics exposition.
3. **Name the sign steps instead of `nlinarith`** (l.60, 64, 88). Each is a one-line positivity fact (`0 < β·x → 0 < x` given `0 < β`; then `0 < (1/β)(S(γ) − S(ρ)) → S(ρ) < S(γ)`). Named hypotheses like `hgap : 0 < (1/β) * (S γ − S ρ)` would let a reader see the inequality logic that `nlinarith` currently hides.
4. **Decouple from CFE's private internals.** The `change` at l.101–104 restates `canonical_matrix`/`canonical_weight` (both `private` in CFE) verbatim and holds only by definitional transparency — it breaks silently if CFE's internal representation changes. Export a public spectral-form lemma from CFE (`(canonical_state H β).matrix = U * diag(w) * U†`) and rewrite with it. Similarly, l.16–31 re-derive CFE's private `hermitian_eigenvalue_diagonal`/`hermitian_spectral_cfe` under new names (and `trace_self_log_eq_neg_entropy` exists twice more, PinchingEntropy l.434 / CFE l.203) — promote one public copy of each.
5. **Extract the unitary-conjugation product step.** The two calc legs at l.119–128 and l.132–138 repeat "`(U X U†)(U Y U†) = U(XY)U†`"; one helper lemma removes both and reads as the actual mathematical fact being used.

## 5. Verdict

The module is in good shape: all four theorems are honest statements of the canonical-ensemble facts they name, the Gibbs relative-entropy identity restatement with `β > 0` is sound (the guard excises exactly the genuinely-false `β = 0` junk case, and the PosDef canonical state keeps every relative-entropy value honest), and the whole module is kernel-verified to depend on none of the project's 4 axioms — a clean result worth stating loudly in the submission docs. Follow-ups, ranked: **(1) soundness-of-presentation, do first:** correct the false "proof debt" module docstring and the stale sibling comments (CFE header, CFE l.266–270, PinchingEntropy l.1073–1076, PROOF_STATUS.md item 4) so the documentation matches the proved state; **(2) robustness:** replace the defeq `change` on CFE's private Gibbs internals with a public spectral-form lemma and deduplicate the private spectral prelude; **(3) polish, do later:** derive max-entropy as a corollary of min-free-energy (or share the gap lemma), name the sign steps, and optionally relax `β > 0` to `β ≠ 0` where only nonzeroness is used.
