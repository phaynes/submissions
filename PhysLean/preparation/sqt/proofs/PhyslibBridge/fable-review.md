# Fable review — `Proofs/PhyslibBridge.lean` (291 lines, 0 axioms)

Reviewed at pinned physlib rev `eb547a5c` (lake-manifest), Lean toolchain v4.31.0.
All claims below about transitive axiom sets were checked by running `#print axioms`
through `lake env lean` against the built project, not by reading alone.

## 1. What this module proves

This is the index-convention bridge between the framework's local API — `DensityMatrix n`
over flattened `Fin (m * n)` indices (via Mathlib's `finProdFinEquiv`) and list-of-Kraus
`CPTPMap n` — and physlib's `MState d` over product index types and bundled `CPTPMap dIn dOut`.
It contains:

- **The framework-wide entropy definition.** `von_neumann_entropy` (lines 21–24), the honest
  spectral formula with an explicit `0·log 0 = 0` guard. Note: the central quantity of the whole
  development is *defined in the bridge module*, not in `BasicDefinitions`.
- **Matrix-level partial trace over the first factor** `partialTrace₁` (27–30) with hermiticity /
  PSD / trace preservation (32–63), and the `DensityMatrix`-level marginals: `partial_trace_A`
  (66), `partial_trace_C` (74), `partial_trace_first` (82), `partial_trace_AC` (99).
- **The state maps** `toMState` (104), `toMStatePair` (113), `finTripleEquiv` (118),
  `toMStateTriple` (125).
- **The transport kit**: entropy agreement (`entropy_toMState` 129, `entropy_toMStatePair` 142,
  `entropy_toMStateTriple` 147) and marginal agreement (`toMStatePair_traceRight` 153,
  `toMStatePair_traceLeft` 163, `toMStateTriple_assoc'_traceRight` 190, `toMStateTriple_traceLeft`
  211, `toMStateTriple_traceLeft_traceRight` 237).
- **The channel bridge**: `toPhysCPTP` (264) and `toPhysCPTP_apply` (275).

This kit is exactly what `PinchingEntropy` consumes to import physlib's proved inequalities into
local vocabulary: `entropy_subadditive` (PinchingEntropy:262), `strong_subadditivity` (:1861),
`araki_lieb_triangle` (:1880), and — via `toPhysCPTP` — `relative_entropy_monotone` /
`relative_entropy_data_processing` (:2158, :2174) from physlib's sandwiched-Rényi DPI at α = 1.
The module is therefore the mechanism by which A2 (strong subadditivity) and relative-entropy
monotonicity enter the proof product.

## 2. Soundness review

**I found nothing unsound.** This module is the cleanest kind of bridge: every theorem is an
equality between two fully concrete closed terms, most proved by `rfl` after a `change`, i.e.
kernel-checked definitional agreement. What I checked, specifically:

1. **Kernel axiom audit (the load-bearing check).** `#print axioms` on all eight bridge theorems,
   on every physlib theorem the framework consumes through this bridge
   (`Sᵥₙ_strong_subadditivity` SSA.lean:1184, `Sᵥₙ_subadditivity` :1196,
   `Sᵥₙ_triangle_subaddivity` :1225, `Sᵥₙ_relabel` VonNeumann.lean:143,
   `sandwichedRenyiEntropy_DPI_eq_one` DPI.lean:1384, `qRelativeEnt_ker`), and on the downstream
   local consumers (`Quantum.strong_subadditivity`, `Quantum.entropy_subadditive`,
   `Quantum.araki_lieb_triangle`, `Quantum.relative_entropy_monotone`,
   `Quantum.relative_entropy_data_processing`): **every one reports exactly
   `[propext, Classical.choice, Quot.sound]`** — no `sorryAx`, no `ofReduceBool`. This matters
   because physlib at this rev *does* contain sorried theorems elsewhere
   (`qRelativeEnt_joint_convexity`, Relative.lean:2119–2122, marked `@[sorryful]`; the whole
   `Entropy/Axiomatized/` subtree; `Axiomatized/Renyi.lean`). None of it leaks into the used chain.
   Physlib's SSA is genuinely proved (weak monotonicity + purification, ~1300 lines), not assumed.

2. **Statement faithfulness / convention agreement.** Verified physlib's semantics against its
   source: `MState.traceLeft` removes the *left* factor and `traceRight` the *right*
   (States/Mixed/MState.lean:575, :582, confirmed by `qConditionalEnt`/`qMutualInfo` usage);
   `relabel e` has entries `old (e i) (e j)` (:1051); `assoc'` is a triple-SWAP composition
   (:1186). The bridge maps these correctly: `traceRight ↦ partial_trace` (traces out the second
   factor; MathsAxioms:61–64 sums the second index), `traceLeft ↦ partial_trace_A` (sums the
   first index), and the tripartite marginals match SSA's `ρ₁₂ = assoc'.traceRight`,
   `ρ₂₃ = traceLeft`, `ρ₂ = traceLeft.traceRight` exactly. The transported
   `Quantum.strong_subadditivity` statement is the honest Lieb–Ruskai form
   `S(AB) + S(BC) ≥ S(ABC) + S(B)` in purely local vocabulary.

3. **The two non-`rfl` index facts are real and small.** `finTriple_left_eq_assoc` (179–188) is
   the mixed-radix associativity identity `c + nC·b + nC·nB·a = (c + nC·b) + (nB·nC)·a` closed by
   `ring`; `toMStateTriple_traceLeft_traceRight` (237–254) needs one `Finset.sum_comm`. The
   private `mstate_assoc'_eq_relabel` (173–177) proves by `rfl` that physlib's triple-SWAP
   associator is definitionally the plain `prodAssoc` reindex — kernel-checked, so no gap there.

4. **No junk-value artifacts.** The only `log 0` surface is `von_neumann_entropy`'s explicit
   guard (redundant given Mathlib's `log 0 = 0`, but honest), and `entropy_toMState` (138–140)
   proves case-by-case that it coincides with physlib's `negMulLog` convention. Entropy is total
   with no support hypothesis, which is mathematically correct — nothing here can make a
   downstream claim vacuously true.

5. **No hidden assumption of what downstream should prove.** `toMState` (104–110) merely
   repackages the four `DensityMatrix` fields; the bridge is used only in the sound direction
   (forward transport of proved physlib inequalities). Nothing assumes surjectivity or an inverse
   map. `toPhysCPTP` requires exactly the local completeness `∑ Kᵢ†Kᵢ = 1` that physlib's
   `of_kraus_CPTPMap` needs, and `toPhysCPTP_apply` pins the action to
   `∑ K ρ K†` on both sides — faithful, no strengthening or weakening.

**One honest caveat (a guard gap, not a proof gap).** The "0 axioms" property of this module —
and hence the framework's headline "axioms = 4" — is only as strong as the *pinned* physlib rev.
`scripts/gen_boundary.sh` greps `axiom`/`sorry` over the local `Proofs/` tree only; `lake build`
stays green when a dependency contains `sorry`. If a future physlib bump routed any consumed
theorem through a sorried lemma (and physlib carries several today), no existing gate would fire,
and the conditional-proof claim would silently weaken. Today's kernel audit says the chain is
clean; nothing *enforces* that tomorrow.

## 3. Axiom-reduction opportunities

The module has no axioms. Three concrete items, in value order:

1. **Add a kernel-level axiom guard (closes the caveat above).** A small Lean file built as part
   of `lake build` (e.g. `Proofs/AxiomGuard.lean` using `#guard_msgs in #print axioms` on the
   exported theorems — `Quantum.strong_subadditivity`, `Quantum.relative_entropy_data_processing`,
   the SQT_Axiom corollaries) asserting the axiom set is exactly the 4 declared axioms plus
   `propext, Classical.choice, Quot.sound`. This upgrades `boundary.json` from a grep-local claim
   to a machine-checked transitive claim, robust across physlib bumps.

2. **The docs undersell what is proved — update them (this *strengthens* the honest claim).**
   `axiom-surface.md` lists "A2 Strong subadditivity — Lieb–Ruskai (1973)" as a paper-level
   assumption "carried as interface/bridge assumptions", and `PROOF_STATUS.md` priority 3 still
   lists "strong subadditivity, Araki-Lieb, monotonicity, subadditivity" as open
   proof-retirement targets. Per the kernel audit, all four are *proved imports* at the current
   pin — only Lieb joint convexity (the 1 declared axiom) remains. The residual trust for A2 is
   statement-faithfulness of physlib + Mathlib (the same trust class as Mathlib itself), and the
   bridge reduces even that: `entropy_toMState` and the marginal-transport theorems prove
   physlib's `Sᵥₙ` and marginals *are* the local spectral/summation definitions.

3. **This module is the discharge lane for the one remaining `PinchingEntropy` axiom**
   (`relative_entropy_jointly_convex`, on-support). Physlib's `qRelativeEnt` is ℝ≥0∞-valued, so
   its *unconditional* joint convexity (`qRelativeEnt_joint_convexity`, the sorried statement
   that PR #1378 proves) is true — `⊤` absorbs support violations — which is exactly why it
   escapes the framework's own kernel-verified refutation of the unconditional *real-valued*
   form. What has to line up for the discharge:
   - (a) PR #1378 merged (or vendored) at the pin, replacing the sorry at Relative.lean:2122;
   - (b) a new bridge lemma here, `toMState_mixture :
     toMState (density_matrix_mixture ρ₁ ρ₂ p h) = p [toMState ρ₁ ↔ toMState ρ₂]`
     (physlib's `Mixable` form) — **this can and should be built now**, so the discharge is a
     ~10-line patch when upstream lands;
   - (c) support bookkeeping for mixtures — physlib's `HermitianMat.ker_weighted_sum_le`
     (DPI.lean:545) does the work;
   - (d) the ENNReal→ℝ `toReal` monotonicity arithmetic — the exact pattern already demonstrated
     in `relative_entropy_monotone` (PinchingEntropy:2158–2172) using
     `qRelativeEnt_toReal_eq_relative_entropy_real` (:2147).

   An upstream-independent alternative — derive joint convexity from the already-imported (and
   kernel-clean) DPI via classical-quantum block states — is possible in principle but awkward
   here: the local `CPTPMap n` is square-only (n → n), while the classical-register partial trace
   is 2n → n, forcing a tensor-with-`|0⟩⟨0|` embedding trick plus a block-diagonal additivity
   lemma for `relative_entropy_real`. The #1378 route is strictly cleaner.

## 4. Legibility / teaching notes

The module is short and already better-structured than most bridge code, but three things would
materially help a reviewer:

1. **The five marginal-transport proofs share an opaque `dsimp`-then-`change` pattern**
   (153–161, 163–171, 190–209, 211–235, 237–254). Each unfolds 8–10 definitions and then
   `change`s the goal into an 8-line wall of explicit double-indexed sums (worst at 201–208 and
   246–253) that the reader must trust is well-typed. Fix shape: state one named entrywise
   unflattening lemma — "`(toMStatePair ρ).m ((a,b),(a',b')) = ρ.matrix (flat (a,b)) (flat (a',b'))`" —
   and its triple analogue as `simp` lemmas; each transport theorem then becomes `ext` plus a
   `simp` whose lemma names *teach the convention* instead of hiding it.
2. **The one real piece of index arithmetic is uncommented.** `finTriple_left_eq_assoc` (179–188)
   is the heart of the associativity bridge — mixed-radix flattening is associative:
   `c + nC·b + nC·nB·a` both ways — but reads as bare `ext; simp; ring`. A docstring displaying
   the identity would let a reviewer verify the whole tripartite bridge from one line. Similarly,
   `mstate_assoc'_eq_relabel` (173–177) is `private` yet is genuinely teaching-worthy (physlib's
   triple-SWAP associator is definitionally a plain reindex, certified by `rfl`); expose it with
   a docstring.
3. **Naming and placement.** `von_neumann_entropy` — the framework's central quantity — lives in
   the bridge file where nobody will look for it; at minimum the module docstring (8–13) should
   say so. The partial-trace names follow no scheme: `partial_trace` (BasicDefinitions:236)
   removes the *second* factor, `partial_trace_A` removes the *first*, and `partial_trace_first`
   is the same operation as `partial_trace_A` at triple arity; `partialTrace₁` lives here while
   its sibling `partialTrace₂` lives in `MathsAxioms`. A convention table in the module header —
   local name ↔ physlib name ↔ "traces out X, keeps Y" — is the cheap fix; renaming is the
   thorough one.

## 5. Verdict

This module is in genuinely good shape — zero axioms, transports that are mostly definitional
`rfl`s, and a kernel audit confirming that everything it imports from physlib (SSA, subadditivity,
Araki–Lieb, relabel-invariance, DPI at α = 1) arrives fully proved, contributing nothing beyond
`propext, Classical.choice, Quot.sound`. The highest-value follow-ups, ranked: **(1)** add the
kernel-level `#print axioms` guard so the clean transitive axiom surface is *enforced* across
physlib bumps rather than incidental (soundness-adjacent; do first); **(2)** update
`axiom-surface.md` / `PROOF_STATUS.md` to claim SSA, Araki–Lieb, subadditivity and DPI-monotonicity
as proved imports — the current wording understates the result; **(3)** pre-build the
`toMState_mixture` bridge lemma now so the last `PinchingEntropy` axiom discharges trivially when
PhysLean PR #1378 lands, and do the legibility pass (entrywise unflattening lemmas, docstrings on
the two private lemmas) at the same time.
