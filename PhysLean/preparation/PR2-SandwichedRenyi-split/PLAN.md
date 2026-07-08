# PR2 — split the sandwiched-Rényi API into its own file

**Origin:** JTS, on PR #1378 (`DPI.lean:1423`): *"In an ideal world I think we would have a
file dedicated to `sandwichedRelRentropy` and this would go in there, the Relative.lean
file is getting a bit long, as is this one."* Follow-up agreed on-thread: *"Yep — let's
leave it for a future PR."* This directory is that future PR's plan and its safety net.

**Single concept:** move the sandwiched-Rényi (`D̃_α`) family — definition, notation,
analytic engine, nonnegativity, additivity, continuity — out of `Relative.lean` (2452
lines) into a new dedicated file. **No statement changes. No proof golf. A move.**

---

## 0. Ground truth (measured at `feat/qrelent-joint-convexity` = `720c9fff`)

### What moves (≈1450 lines out of 2452)

| Cluster | Lines (at 720c9fff) | Content | Privacy |
|---|---|---|---|
| Analytic prelude | ~26–441 | `sandwiched_trace_pos/of_lt_1/of_gt_1`, Jensen/Hölder (`weighted_jensen_rpow`, `doubly_stochastic_holder`), `HermitianMat` rpow/supportProj helper lemmas, nonneg α-cases, `trace_at_one` | mostly `private`; ~10 public `HermitianMat.*`/Jensen lemmas |
| Derivative engine | ~448–1178 | `hasDerivAt_trace_rpow_at_one` … `limit_at_one`: `eigenWeight` machinery, `B_of` continuity, uniform rpow-slope limits, `hasDerivAt_trace_at_one` | all `private` |
| Public nonneg | 1179 | `sandwichedRelRentropy_nonneg` | public |
| Def + notation | 1462–1495 | `sandwichedRelRentropy_additive_alpha_one_aux`, **`def SandwichedRelRentropy`**, **`notation D̃_`** | public |
| Additivity | 1505–1613 | `_additive_alpha_one` (priv), `sandwiched_term_product`, `_additive_alpha_ne_one`, `_additive`, `_relabel`, `_self`, `sandwichedRelEntropy_ne_top` (sic) | mixed |
| Continuity | 1646–1780 | `continuousOn_Ioi_1(_aux)`, `continuousOn_Ioo_0_1(_aux)`, `continuousAt_1` (priv), **`sandwichedRelRentropy.continuousOn`** (public) | mixed |
| Congruence | 1814–1857 | `_of_unique`, `_heq_congr`, `_congr` | public |
| From DPI.lean | DPI:1423 | `sandwichedRelRentropy_tendsto_qRelativeEnt` — **see D3**: statement mentions `𝐃`, cannot move verbatim | public |

### What stays in `Relative.lean` (≈1000 lines)
`def qRelativeEnt` + `𝐃` notation (1497–1500), `qRelativeEnt_ker` / `_ne_top_iff` /
`_eq_top_iff`, `_eq_neg_Sᵥₙ_add`, `_relabel`, `_additive`, both `lowerSemicontinuous`
sections, `qRelEntropy_self`, `_ne_top`, `_rank`, `_op_le`, and the α=1 auxiliaries that
are genuinely about `𝐃`.

### Measured couplings (the traps)
1. **Stay-behind uses cluster privates.** The `lowerSemicontinuous` sections use
   `inner_cfc_eq_sum_eigenWeight`, `eigenWeight_nonneg`, `eigenWeight_zero_of_eigenvalue_zero`
   (currently `private`, in the derivative engine). → these get **promoted to public** in
   the new file (they are genuinely reusable spectral-weight lemmas). Every promotion is
   listed in `harness/allowed-changes.txt`; the harness fails on any *unlisted* privacy change.
2. **`qRelativeEnt := D̃_1`** — Relative.lean will `public import` the new file; the def
   stays put (D2).
3. **Downstream consumers (7 files):** `Entropy/DPI`, `Channels/Pinching`,
   `ResourceTheory/{FreeState,HypothesisTesting,SteinsLemma}`,
   `ForMathlib/HermitianMat/{LogExp,Proj}` (the last two are definition sites of helpers,
   not consumers). Because Lean's `public import` re-exports, **no downstream file should
   need any edit** — the harness proves this (H5).
4. **Section/variable scoping:** the additivity `section` (1189–1561) contains BOTH
   sandwiched material AND `qRelativeEnt`'s def. Chunks must carry their `variable`/`open`
   context; the new file reconstructs the same headers.

---

## 1. Decision points (settle before P2; recommendations marked)

- **D1 — file name.** `QuantumInfo/Entropy/SandwichedRenyi.lean` *(recommended — siblings
  are concept-named: VonNeumann, Relative, DPI, SSA)* vs `SandwichedRelRentropy.lean`.
- **D2 — does `qRelativeEnt`'s definition move?** **Recommend: stays in Relative.lean.**
  It is one line (`:= D̃_1`) and every 𝐃 theorem stays with it; the new file is then purely
  the α-family. (Alternative — def moves too — makes the new file self-contained for the
  tendsto lemma but guts Relative.lean's identity as "the relative entropy file".)
- **D3 — the tendsto lemma.** Its statement `D̃_α → 𝐃(ρ‖σ)` mentions `𝐃`, defined above
  the new file, so it cannot move verbatim. **Recommend:** state the family-pure version in
  the new file — `sandwichedRelRentropy_tendsto_one : Tendsto (fun α => D̃_α(ρ‖σ)) (𝓝[>] 1)
  (𝓝 (D̃_1(ρ‖σ)))` — and keep the existing public name in Relative.lean as a one-line
  alias (`:= sandwichedRelRentropy_tendsto_one ρ σ`, defeq since `𝐃 = D̃_1`), so DPI's
  proof and the existing name/statement survive byte-identical. The alias is a whitelisted
  inventory addition.
- **D4 — the ~10 public general-purpose `HermitianMat.*`/Jensen lemmas** in the prelude.
  **Recommend: move with the cluster** (single-concept PR), and *offer* in the PR body to
  relocate them to `ForMathlib/HermitianMat/` as a further follow-up if preferred.

---

## 2. Sequencing / preconditions

- **P0.a — PR #1378 must land first** (this refactor moves code #1378 adds, and touches the
  same files). Until it merges: branch from `feat/qrelent-joint-convexity` (`720c9fff`);
  after merge: rebase onto `master` and re-run the baseline.
- **P0.b — green start:** `lake build` full-library green; `git status` clean.
- **P0.c — capture the baseline:** `harness/10_baseline.sh` (text artifacts instantly;
  `--axioms` needs a built env). Commit `harness/baseline/` — the PR reviewer can re-run
  the check against it.

## 3. Step-by-step (each phase = one commit; any red gate ⇒ `git reset --hard` to previous)

| Phase | Action | Gate |
|---|---|---|
| **P1** | Run `harness/00_manifest.sh` → mechanical move-manifest (decl → lines). Human-review it; finalize D1–D4 into `allowed-changes.txt`. | manifest reviewed & committed |
| **P2** | Create the new file: copyright header (match house style), `module`, imports = Relative.lean's current imports, `@[expose] public section`, `noncomputable section`, same `variable` block, `/-! ... -/` module doc. Register in `QuantumInfo.lean` (`public import`, placed before Relative). | `lake build` green (empty-file sanity) |
| **P3** | Move the analytic prelude (~26–441) verbatim. | `lake build QuantumInfo.Entropy.Relative` green |
| **P4** | Move the derivative engine (~448–1178) + `sandwichedRelRentropy_nonneg`. Apply the whitelisted `eigenWeight` promotions (private → public). | build green |
| **P5** | Move def + notation + additivity cluster (1462–1495, sandwiched parts of 1505–1613), reconstructing section/variable context; Relative.lean gains `public import <new file>`. | build green |
| **P6** | Move continuity cluster (1646–1780) + the **three** congruence lemmas *by name* (`sandwichedRelRentropy_of_unique`, `_heq_congr`, `_congr`). **NB (Codex B3):** the ~1814–1857 region is INTERLEAVED — `qRelEntropy_of_unique`, `qRelEntropy_heq_congr`, `qRelativeEnt_rank`, `qRelativeEnt_ker` mention `𝐃` and STAY. Never move this region by line range; move only the three `sandwichedRelRentropy_*` names. | build green |
| **P7** | D3: add `sandwichedRelRentropy_tendsto_one` to the new file; convert the DPI-added `sandwichedRelRentropy_tendsto_qRelativeEnt` into the one-line alias **in Relative.lean**; delete it from DPI.lean. | build green (incl. DPI) |
| **P8** | Full verification: `harness/20_check.sh` (inventory ∪ fidelity ∪ axioms ∪ diff-shape), `lake build` (full), `lake exe lint_all`, `scripts/lint-style.sh` (commit first — it reads committed state). | **all green** |
| **P9** | PR packaging: body = "pure move" claim + harness evidence (auto-generated inventory table, the whitelist, axiom-surface diff = empty). Commit trailers per AGENTS.md (Signed-off-by Philip; Co-authored-by Helios/Claude/... `@helios.local`). Philip pushes fork + opens PR. | verify.sh-style checks in PR body reproducible |

**Estimated shape:** new file ≈ 1450–1500 lines; Relative.lean ≈ 1000; DPI.lean −7.
Net diff ≈ ±0 lines beyond the alias + imports + headers.

## 4. Test harness suite (in `harness/`)

The failure modes of a move-refactor and the harness that catches each:

| # | Failure mode | Harness |
|---|---|---|
| H1 | A declaration silently **dropped or duplicated** | `20_check.sh`: declaration inventory (name+kind) across the affected file-set must be **set-equal** to baseline (modulo `allowed-changes.txt` additions, e.g. the D3 alias) |
| H2 | A statement **accidentally edited** during the move | statement-fidelity: for every decl, the block from its attributes/`private` keyword through `:=` is extracted, whitespace-normalized, hashed; hashes must match baseline **regardless of which file the decl now lives in** |
| H3 | **Axiom/soundness drift** (a proof silently picks up `sorryAx`, or an axiom set changes) | `#print axioms` on **every public theorem** in the blast-radius file-set (auto-derived, not hand-picked — incl. SteinsLemma/HypothesisTesting), compared line-by-line to baseline. Kernel-level, ungameable |
| H4 | Build/lint breakage | full `lake build`, `lint_all`, `lint-style.sh` (P8) |
| H5 | **Unplanned downstream edits** | diff-shape check: `git diff --name-only` vs the planned file list (new file, Relative, DPI, QuantumInfo.lean). Any other file ⇒ FAIL |
| H6 | **Privacy drift** | inventory records the `private` flag; any change not in `allowed-changes.txt` ⇒ FAIL |

Scripts:
- `harness/lib.sh` — shared extractor (declarations, statement hashes, privacy flags)
- `harness/00_manifest.sh` — emit the mechanical move-manifest for review (P1)
- `harness/10_baseline.sh [--axioms]` — capture baseline artifacts into `harness/baseline/`
- `harness/20_check.sh [--axioms]` — recompute + diff vs baseline; exit 0 iff all pass
- `harness/allowed-changes.txt` — the explicit whitelist (reviewed in P1)

**Known extractor limitations** (documented in `lib.sh`): declarations not matching the
`theorem|lemma|def|instance|structure|notation|axiom` head pattern (e.g. `instance :` with
no name, `where`-blocks) are inventoried by position-hash only; the P1 human review of the
manifest is the compensating control.

## 5. Risks & mitigations

- **Section/variable context loss** (moved chunk loses an ambient `variable {α : ℝ}` or a
  local `open Classical in`) → compile gate per phase catches it immediately; chunks are
  whole clusters, never partial sections.
- **`@[simp]`/attribute loss** → attributes are part of the H2 statement block; hash drift ⇒ FAIL.
- ~~The `B_of` definition~~ **RESOLVED**: located by the harness extractor — it is a
  `private abbrev` (hence invisible to the earlier `theorem|lemma|def` grep); it moves with
  the derivative engine (P4).
- **#1378 review changes race** → if JTS requests further #1378 changes, re-run baseline
  after they land; the harness is cheap to re-capture.
- **`sandwichedRelEntropy_ne_top` name typo** (upstream's existing "RelEntropy" spelling at
  1613) → moved **verbatim**, typo and all; renames are out of scope for a move PR.

## 6. What this PR deliberately does NOT do (offer as future work in the PR body)

- Relocate the general `HermitianMat` lemmas to `ForMathlib/` (D4 offer).
- Rename anything (incl. the `RelEntropy` typo) or golf any proof.
- Split DPI.lean's `Q̃_α` trace-functional machinery (a separate concept; JTS noted DPI is
  long too — that's PR3 material if he wants it).

---

## 7. Codex review resolutions (see CODEX-REVIEW.md)

Codex reviewed this plan + harness against the live `720c9fff` checkout and typechecked
the D3 alias (confirmed: `𝐃 = D̃_1` is a transparent `def`, so
`exact sandwichedRelRentropy_tendsto_one ρ σ` proves the `𝐃`-worded statement by defeq —
D3 is sound). Four blocking items, all resolved here:

- **B1 (harness) — `notation` handling.** Notation commands have no `:=`; the extractor
  must not let one swallow the following declaration. **Fix:** `lib.sh` treats `notation`
  as a single-line command; `10_baseline.sh` self-tests that `qRelativeEnt`,
  `SandwichedRelRentropy`, and `sandwichedRelRentropy_additive_alpha_one` are all present
  in the inventory (fail-fast if the extractor regresses). *(The smoke test already showed
  these present, but the self-test makes it a hard gate.)*

- **B2 (harness) — H3 vs whitelisted additions.** New public names
  (`sandwichedRelRentropy_tendsto_one`) and promoted lemmas (`eigenWeight_nonneg`, …) are
  not in the axiom baseline, so a strict diff would false-fail. **Fix:** `20_check.sh
  --axioms` excludes `add`/`promote` names from the strict baseline diff, then separately
  asserts each excluded name's axiom set contains **no `sorryAx`** (and equals an expected
  clean base). No axiom regression can hide.

- **B3 (plan) — interleaved congruence region.** Fixed in P6 above: move the three
  `sandwichedRelRentropy_*` congruence lemmas **by name**, never the 1814–1857 line range
  (it interleaves `qRelEntropy_*`/`qRelativeEnt_rank`/`qRelativeEnt_ker`, which stay).

- **B4 (harness) — elaborated-type drift (THE key gap).** Source-identical text can
  elaborate to a *different type* if the ambient `variable`/instance/universe/scoped-open
  context differs between old and new file — invisible to source-hash, build, and
  `#print axioms`. **Fix:** add a kernel signature check —
  `harness/sig_check.lean` prints `@[decl]`'s `ConstantInfo.type` with `pp.all`/
  `pp.universes`/explicit-implicits for every public moved/affected declaration;
  `20_check.sh` hashes that and diffs vs baseline. This is the real "pure move" guarantee.

Also applied:
- **`open scoped Topology`** must be in scope at the D3 alias site in `Relative.lean`
  (the `𝓝[>]` notation). Verify/add in P7.
- **H1 multiset** (not just name-set) so a private helper duplicated across old+new files
  is caught.
- **Baseline `rev`** is captured AFTER the harness/allowlist artifacts are committed, so
  H5's diff-shape does not flag the harness itself.

Feasibility (Codex): "mechanical-but-careful, not mathematically hard… a competent Lean
engineer can do it with ordinary tools." **No Fable required — Opus executes, build-gated;
Codex reviewed.** The tricky parts are exactly the four above, now guarded.
