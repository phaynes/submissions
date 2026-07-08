**Verdict**
The Lean move is sound in principle. I typechecked the D3 pattern against the live `720c9fff` checkout: a family theorem ending at `𝓝 (D̃_ 1(ρ‖σ))` can prove the old theorem ending at `𝓝 𝐃(ρ‖σ)` by `exact sandwichedRelRentropy_tendsto_one ρ σ`. `qRelativeEnt` is a transparent `def`, so this is definitional equality, not a fragile rewrite.

The plan needs a few fixes before execution, and the harness needs repair before it can be trusted.

**Blocking Issues**
1. **The harness extractor mishandles `notation`.**
   Why: `notation` commands do not contain `:=`, but `lib.sh` waits for `:=`. In this file, the `D̃_` notation would swallow the following `qRelativeEnt` declaration, and the `𝐃` notation would swallow the next theorem. That invalidates H1/H2.
   Fix: parse `notation` as a single command ending on that line or on `=>`, or track notation commands separately. Add a self-test that confirms `qRelativeEnt` and `sandwichedRelRentropy_additive_alpha_one` appear in the inventory.

2. **H3 cannot pass as written once public additions/promotions happen.**
   Why: `sandwichedRelRentropy_tendsto_one` is a new public theorem, and promoted lemmas like `eigenWeight_nonneg` become public. `20_check.sh --axioms` prints current public theorem axioms and diffs against a baseline that did not include those public names.
   Fix: filter `ALLOW_ADD` and `ALLOW_PRO` names from the strict baseline diff, then separately assert their axiom sets contain no `sorryAx` and match an explicit expected list.

3. **The “congruence cluster” includes q-relative declarations that cannot move.**
   Why: the line range around 1814-1857 includes `qRelEntropy_of_unique`, `qRelEntropy_heq_congr`, and `qRelativeEnt_rank`, which mention `𝐃`. These must stay in `Relative.lean` if `qRelativeEnt` stays there.
   Fix: move only `sandwichedRelRentropy_of_unique`, `sandwichedRelRentropy_heq_congr`, and `sandwichedRelRentropy_congr`; keep the q-relative wrappers in `Relative.lean`.

4. **H2 does not catch elaborated statement drift.**
   Why: source text can be identical while ambient `variable`, typeclass, universe, or scoped notation context changes the elaborated type. Build and `#print axioms` do not catch this.
   Fix: add a kernel signature check for public declarations: generate `#check @decl` or a small Lean meta script over `ConstantInfo.type` with `pp.all`, `pp.universes`, and explicit implicits, then hash that output. This is the main missing guard.

**Important Improvements**
- The D3 alias is sound, but remember `𝓝[>]` needs `open scoped Topology`; `Relative.lean` currently does not have that in the top scoped-open list.
- Promoting the spectral-weight lemmas is the right minimal choice. Moving the lower-semicontinuity consumer would force either a cycle or moving `qRelativeEnt`, which is a larger refactor. Add docstrings for promoted public defs/lemmas, especially `eigenWeight`.
- H2 only hashes declaration heads, not proof bodies. That is fine for API fidelity, but not enough to prove “pure move” literally. Add either full declaration-body hashes for moved declarations or rely on `git diff --color-moved` as PR evidence.
- H1 should compare declaration multisets, not only name sets. Private declarations duplicated across old/new modules can compile with the same short source name.
- Ensure `META.rev` is the committed baseline after the harness/allowlist/baseline artifacts are in place; otherwise H5 will flag the harness itself.

**Feasibility**
This is mechanical-but-careful, not mathematically hard. The genuinely tricky parts are the mixed `D̃_α`/`𝐃` region, the private-helper promotions, the `notation`/scope handling, and proving the public API did not drift. A competent Lean engineer can do it with ordinary tools: editor, git, `lake build`, `#check @...`, and `#print axioms`.

Most likely execution bites: the q-relative wrappers accidentally moved, missing `open scoped Topology`, and the current harness giving false confidence because H1/H2 are broken around notation.
