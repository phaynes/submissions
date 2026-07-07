# Fable review — `Proofs/CPTPEmbedding.lean` (566 lines, 0 axioms)

Reviewed: 2026-07-08. Sources read: full module; `Proofs/BasicDefinitions.lean` and
`Proofs/MathsAxioms.lean` (its only project imports, both axiom-free); downstream usage in
`PinchingEntropy.lean`, `CoherentFreeEnergy.lean`, `PhyslibBridge.lean`, `ClassicalLimit.lean`,
`Correspondence.lean`; `control/boundary.json`; sampled `control/axiom-ledger.discharged.ndjson`
(13 CPTPEmbedding rows, all `true_routine_debt`, all now theorems); the public writeup
(`docs/publication/sqt-conditional-proof-writeup.md`) and `overview/axiom-surface.md` claims
touching this module. Analysis only; no source edits.

## 1. What this module proves

CPTPEmbedding is layer 2 of the DAG: it supplies the channel formalism everything above it
consumes, and it carries the paper's "Theorem 3.1" (classical stochastic dynamics embed as
quantum channels). Since its two imports are axiom-free, **every theorem in this module is
unconditional and kernel-checked** — none of the 4 remaining axioms enters here.

Content in four groups:

- **Channel well-formedness (the load-bearing part).** `CPTPMap` (l. 23–25: a Kraus list with
  the completeness relation `∑ Kᴴ K = 1`), `kraus_sum` (l. 158), and the three theorems that
  make `CPTPMap.apply` (l. 232–237) a `DensityMatrix → DensityMatrix` map:
  `kraus_sum_hermitian` (l. 163), `kraus_sum_posSemidef` (l. 175), `cptp_trace_preserving`
  (l. 188). This is what downstream actually uses: `PinchingEntropy` (data-processing via
  `Φ.apply`, `support_le_cptp`, the `dephasing_channel` at l. 2182), `CoherentFreeEnergy`
  (`coherence_monotone_incoherent`, l. 315), and `PhyslibBridge.toPhysCPTP` (l. 264), which
  converts the local structure into physlib's bundled `CPTPMap` using exactly the
  `completeness` field.
- **The stochastic embedding (Theorem 3.1).** `ket_bra` algebra (`ket_bra_mul` l. 57,
  `ket_bra_resolution_identity` l. 90), Kraus family `K_ij = √(Γ_ij)|i⟩⟨j|` (l. 36–43),
  `embedding_is_cptp` (l. 104: column-stochastic Γ gives a complete Kraus family),
  `cptp_from_stochastic` (l. 152), `mul_stochastic` (l. 433), and functoriality
  `embedding_preserves_composition` (l. 452: embedding Γ₂·Γ₁ = composing the embeddings).
- **Unitality.** `is_unital` (l. 290, defined as fixing the maximally mixed state),
  `unital_kraus_condition` (l. 300: unitality forces `∑ K Kᴴ = 1`), `is_doubly_stochastic`
  (l. 294, an alias).
- **Support lemmas.** `unitDM` (l. 240), `partial_trace_tensor` (l. 248: tr₂(ρ⊗τ) = ρ),
  `CPTPMap.compose` (l. 336, with proven completeness), `CPTPMap.id` + laws (l. 398–414),
  `trace_unitary_conj` (l. 417), and the deliberately-weak `stinespring_exists` (l. 279).

## 2. Soundness review

**Bottom line: I found no unsound statement in this module.** No `axiom`/`sorry`/`admit`, no
`True`-valued goals, no zero/one stub standing in for a real quantity (`unitDM` is genuinely
the unique 1-dimensional density matrix, not a stub). What I checked, statement by statement:

- **Hypotheses are all load-bearing.** `kraus_operator_dagger_mul` (l. 78) needs `0 ≤ Γ i j`
  precisely because `√` would junk-collapse on negatives — the hypothesis is honest and used
  (`Real.mul_self_sqrt h`, l. 87). `embedding_is_cptp` uses both halves of `IsStochastic`
  (nonnegativity at l. 123, column sums at l. 144–146). No vacuous quantifier: `IsStochastic`
  is inhabited (e.g. the identity; `Correspondence.dynSwap` gives a checked instance of the
  same column convention).
- **Conventions are consistent.** `IsStochastic` (l. 28) is *column*-stochastic
  (`∀ j, ∑ i, Γ i j = 1`), matching `Correspondence.StochasticDynamics.Γ_stoch` and the action
  formula proved inside `embedding_preserves_composition`: the embedded channel takes the
  diagonal to `(Γ ·ᵥ diag ρ)ᵢ = ∑ⱼ Γᵢⱼ ρⱼⱼ` — probability vectors as columns throughout.
- **`is_unital` via the maximally mixed state** (l. 290) is equivalent to the textbook
  `Φ(I) = I` for these maps because `kraus_sum` is linear in the state; the scaling argument
  is exactly what `unital_kraus_condition` proves, correctly using `NeZero n`. Defining
  `is_doubly_stochastic := is_unital` (l. 294) is right for trace-preserving maps and the
  docstring says it is a representation choice. Neither is used downstream today.
- **`stinespring_exists` (l. 279–285) is weak by design and honestly labelled.** The statement
  quantifies `∃ m U, ∀ ρ, ∃ σ` with `_U` unused and `σ` re-picked per ρ, so it asserts only
  "every output state has a trivial extension" — proved with `m = 1`, `U = 1`,
  `σ = Φ(ρ) ⊗ unitDM`. The 7-line docstring (l. 272–278) states this defect plainly, and the
  `#print axioms` audit marker (l. 287) confirms it is axiom-free. Crucially, **nothing
  downstream uses it** (verified by grep across all 11 modules), so the weakness cannot
  contaminate any other result.
- **One definitional assumption to state, not fix:** `CPTPMap` *defines* channels as
  Kraus-presented families. The Choi–Kraus direction (every completely positive map has such a
  presentation) is neither proved nor needed — all channels in the development are constructed
  in Kraus form — but a reader should be told that "CPTP" here means "given by Kraus operators
  with `∑KᴴK = 1`", i.e. complete positivity holds by construction and the representation
  theorem is out of scope. The module docstring does not currently say this.

**Two claim-surface findings (documentation, not Lean):**

1. **The overview's A1 wording can mislead.** `overview/axiom-surface.md` (§ "paper-level
   assumptions imported elsewhere") lists *A1 Stinespring dilation — every CPTP map has a
   unitary dilation* and adds "`stinespring_exists` was discharged to a theorem…". Same
   phrasing in `proof-map.md` layer 2 ("CPTP maps, Stinespring, the embedding theorem") and
   the writeup's module table ("… stochastic embedding, Stinespring, composition"). A reader
   will conclude Stinespring's theorem is proved. It is not: the discharged statement is the
   weakened per-state form, and genuine Stinespring is currently **neither assumed, nor
   proved, nor needed** anywhere in the development. That last fact is *stronger and better*
   than "carried as an interface assumption" — the docs should say exactly that. (The writeup
   line 28 does call it "trivially-true / vacuous", so the honest signal exists; it just needs
   to be the only signal.)
2. **The writeup's CPTPEmbedding paragraph is stale in the safe direction.** Writeup §2 says
   "The main completeness and composition obligations remain explicit" — false since the
   discharge campaign: `embedding_is_cptp` and `embedding_preserves_composition` are
   kernel-checked theorems (ledger rows confirm they were once axioms). Understatement is not
   a soundness risk, but a reviewer who diffs prose against code will lose trust in the
   accurate claims too.

## 3. Axiom-reduction opportunities

No axioms live here, and nothing in this module blocks the remaining 4 (those sit in
`PinchingEntropy` and `SQT_Axiom`). Tightening opportunities on implicit assumptions:

- **Make `stinespring_exists` honest or retire it.** Two concrete paths if the development
  ever needs real Stinespring: (a) check physlib — the bridge already consumes its bundled
  `CPTPMap` (`of_kraus_CPTPMap`, `MatrixMap.of_kraus`), and if it carries a dilation theorem,
  import rather than re-axiomatize; (b) for the only channels this development constructs
  (`cptp_from_stochastic Γ`), a *universal* dilation is directly provable with in-module
  ingredients: `V|j⟩|0⟩ = ∑ᵢ √(Γᵢⱼ) |i⟩|i⟩` is an isometry exactly because Γ is
  column-stochastic (the same computation as `embedding_is_cptp`), and extends to a unitary on
  the n·n-dimensional dilation space. That would replace the vacuous statement with a true
  Stinespring instance for the SQC embedding — a genuine strengthening, medium effort. Until
  then, renaming (or moving to an `Audit`/`Vacuous` namespace) prevents miscitation.
- **Shrink the bespoke trusted surface via Mathlib.** `ket_bra n i j` is Mathlib's
  `Matrix.single i j (1 : ℂ)` (née `stdBasisMatrix`), and `ket_bra_conjTranspose` /
  `ket_bra_mul` / `ket_bra_resolution_identity` correspond to existing `StdBasisMatrix` API
  (transpose/conj lemmas, `mul_same`/`mul_of_ne`, and the diagonal-sum identity). Aligning
  removes ~50 lines of hand-rolled basis algebra and rests the embedding on library lemmas.
  Similarly `trace_unitary_conj` duplicates what `Matrix.trace_mul_comm` + `unitary` API give;
  note `CoherentFreeEnergy` (l. 77–88) already had to re-prove the same fact privately for
  `Matrix.unitaryGroup` — a symptom of the local `UnitaryMatrix` structure vs Mathlib's
  unitary group coexisting. Picking one representation would delete both copies.
- **Close the `CPTPMap.compose` semantic gap.** `compose` (l. 336) proves completeness of the
  composite Kraus family but there is no lemma `(Φ₁.compose Φ₂).apply ρ = Φ₂.apply (Φ₁.apply ρ)`
  — the fact that composition *is* composition. Today `compose` is unused (functoriality of
  the embedding is proved directly, l. 452), so this is latent, but any future user assuming
  the opposite order (`Φ₁ ∘ Φ₂`) would get reversed dynamics with no theorem to catch it. A
  one-lemma fix plus a docstring naming the diagram order ("Φ₁ first").

## 4. Legibility / teaching notes

The proofs are mostly clean calc-style and read well. The top issues, in order of impact:

1. **The file's self-description is wrong, and harmfully so.** The module docstring
   (l. 7–15) says "hard obligations are made explicit as axioms and tracked in
   `control/proof-debt-ledger.ndjson`", and the section header "Restart proof obligations"
   (l. 45–49) says the following results are "the Stage 2 proof queue, not accepted final
   mathematics". Both predate the discharge campaign: the module now has **zero** axioms and
   everything below is kernel-checked. A teaching reader hits this header before any theorem
   and is told not to trust what follows. Rewrite the header as "everything below is proved;
   the 'Discharged (was an axiom)' docstrings record provenance".
2. **Extract the buried action formula.** `h_apply_matrix` (l. 458–521, ~60 of the 113 lines
   of `embedding_preserves_composition`) proves the module's most citable semantic fact: the
   embedded channel acts as `ρ ↦ diag(Γ ·ᵥ diag ρ)` (dephase, then push forward). As a named
   top-level theorem it (a) turns functoriality into a short 3-step calc mirroring the paper
   argument, (b) is precisely the bridge `ClassicalLimit.embed_prob` needs for the missing
   "embedded channel ∘ embedded distribution = embedded pushforward" statement — currently the
   classical-limit layer and the CPTP layer never touch, and this one lemma joins the two
   halves of the SQC story. The inner `hkb` (l. 463–468, `|i⟩⟨j| M |j⟩⟨i| = M_jj |i⟩⟨i|`)
   deserves the same treatment next to `ket_bra_mul`.
3. **Delete duplicated machinery.** `hdensity` (l. 557–564) re-proves
   `DensityMatrix.matrix_ext` (BasicDefinitions l. 34–36) inline. The
   `change`/`List.map_map`/`Finset.sum_map_toList` boilerplate converting the list-sum over
   `stochastic_kraus` into a Finset double sum appears twice (l. 107–130 and l. 482–505); one
   helper lemma removes both and makes each proof start at the mathematics.
4. **Small polish.** `kraus_preserves_hermitian` (l. 426) is unused — either use it inside
   `kraus_sum_hermitian` (which would make that proof read as "each term is Hermitian, sums of
   Hermitians are Hermitian") or drop it. Document the argument-order conventions on
   `mul_stochastic` (hypotheses (Γ₁, Γ₂), conclusion Γ₂·Γ₁) and `compose`. Decide a uniform
   policy for in-source `#print axioms` audit markers (l. 287) before submission.

## 5. Verdict

This module is in good shape: zero axioms, fully unconditional, statement-level semantics
faithful to the standard facts they name, hypotheses all load-bearing, conventions consistent
with the correspondence module, and the one deliberately weak statement
(`stinespring_exists`) is honestly documented in-file and provably uncontaminating (zero
downstream uses). The highest-value follow-ups, ranked: **(1) claim hygiene (do first):** fix
the stale in-file "restart obligations" narrative (l. 7–15, 45–49) and reword the
`axiom-surface.md`/`proof-map.md`/writeup mentions of "Stinespring" so no reader can conclude
the dilation theorem was proved — state instead that genuine Stinespring is neither assumed
nor needed; consider renaming the weak theorem. **(2) structural legibility:** extract
`h_apply_matrix` as the named channel-action theorem and use it to connect
`cptp_from_stochastic` to `ClassicalLimit.embed_prob`, closing the currently-missing
classical–quantum agreement statement; add the `compose`-applies-as-composition lemma.
**(3) polish (later):** migrate `ket_bra` onto Mathlib's `stdBasisMatrix`/`single` API, unify
the two unitary representations to delete the duplicated trace-conjugation lemma, and dedupe
the pair-sum boilerplate.
