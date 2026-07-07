# How to open the invited PR — updated for the Codex-refined refactor

This is the operator playbook for opening the PhysLean pull request from the **current**
state of the proof (commit `f901e353`, the refactor JTS's "golf it a bit" note prompted,
plus a Codex second-opinion pass). It is a delta on top of what `submit.sh` and
`PR-BODY.md` already give you — read this first, then let `submit.sh` walk the mechanics.

Per PhysLean `AI-POLICY.md` §3.1, **you** open the PR and post to Zulip; no agent does.
Nothing in this packet has been pushed anywhere.

---

## 0. What changed since JTS last saw it

He reviewed the first proof (commit `33cb766e`) and said: *"These look good, although you
may want to golf them a bit. There are lots of `have` statements, the number of which can
probably be reduced."*

The current commit `f901e353` is the response:

- **Idiom polish** — collapsed the mechanical `have`s that read as beginner/AI Lean.
- **Finiteness API** — `qRelativeEnt_ne_top_iff` / `qRelativeEnt_eq_top_iff` (Relative.lean),
  replacing five inline unfoldings of the `𝐃` definition.
- **Structural split per the repo's 50-LOC proof-structure rule** — the `Fin 2` mixture
  plumbing, the `α → 1⁺` continuity step, and the `ENNReal.ofReal` convex-combination
  identity are each their own small documented `private` lemma; the main theorem body
  dropped from ~20 named `have`s to ~10 and reads as *degenerate → ⊤ → limit*.
- **API-gap fill** — `@[simp] Mixable.mix_one` (Prob.lean), the missing partner of the
  existing `@[simp] mix_zero`; both degenerate weight cases now close by `simp`.

This is exactly the "reduce the `have`s / extract with meaning" direction his note and the
repo's `AGENTS.md` both point at. The **theorem statement is byte-identical** to what he
already saw; only the proof and its supporting API changed.

**Second-opinion pass**: the refactored proof was additionally reviewed by Codex (gpt-5.5,
via the Helios model bridge). It judged the refactor "already close to expert quality,"
declined speculative `gcongr` golf, and suggested three small improvements — two were
applied (deriving `eq_top_iff` from `ne_top_iff`; making the high-arity convexity call
explicit), one was rejected as incorrect (it wrongly thought a `set … with` binding was
unused — it is used twice). All build-verified.

---

## 1. Verification state of `f901e353` (already run; re-runnable)

| Check | Result |
|---|---|
| Statement byte-identical to the original stub | ✅ (`verify.sh` step 1) |
| `#print axioms qRelativeEnt_joint_convexity` | ✅ `[propext, Classical.choice, Quot.sound]` — no `sorryAx` |
| `lake build QuantumInfo` (full library — gates the new `@[simp]`) | ✅ 8636 jobs |
| `lake exe lint_all` | ✅ zero findings in the 3 changed files (4 pre-existing transitive-import flags in untouched `Physlib/SpaceAndTime/*`; this PR adds no imports) |
| `scripts/lint-style.sh` | ✅ clean |

Re-confirm any time with: `./verify.sh /path/to/physlib` (add `LINT=1` for the linters).

---

## 2. The commit is on your branch, unpushed

- Branch `feat/qrelent-joint-convexity` in `physlib-contrib` is at **`f901e353`**.
- It carries the required trailers: `Signed-off-by: Philip Haynes` (author), and
  `Co-authored-by:` lines for `Helios`, `Claude Opus 4.8`, and `Codex gpt-5.5`
  (AGENTS.md "Commits" requires the AI co-author line; addresses use `@helios.local`
  placeholders, no vendor domains).
- The repo's only git remote is upstream `leanprover-community/physlib` — so there is **no
  fork remote configured**. Before pushing you must either add your fork as a remote or let
  `submit.sh` step 3 push to a fork it helps you set. **Do not push the branch to the
  upstream `origin`.**

> If you amend the commit for any reason (e.g. to reword), the hash changes; then update
> `EXPECTED_COMMIT` in `submit.sh` and re-run `verify.sh`.

---

## 3. Open the PR — use the guided script

```bash
cd /Volumes/second-store/devel/knowledge-base-mcp/submissions/PhysLean/submitted/Proof-Joint-convexity-of-the-Umegaki-quantum-relative-entropy
./submit.sh /Volumes/second-store/devel/knowledge-base-mcp/mentormind/physlib-contrib
```

It is interactive and prompts (y/N) before every outward-facing step. It will:
0. check you are on `feat/qrelent-joint-convexity` at `f901e353`, clean tree, `gh` authed;
1. run `verify.sh` (+ `LINT=1`);
2. run `lint_all` and `lint-style.sh` directly;
3. ask how to publish the branch — **choose your fork** (not a direct upstream push);
4. push the branch to your fork;
5. open the PR **non-draft** with the title + `PR-BODY.md`, tag `t-quantumInfo`;
6. print the follow-up checklist.

Title (already in `PR-BODY.md`): `feat(QuantumInfo): prove qRelativeEnt_joint_convexity`

---

## 4. PR body & comments

- **Body**: `PR-BODY.md` → the fenced ```markdown block under "**Body**". It now lists all
  added declarations (incl. `mix_one`, the two `_top_iff` lemmas, and the private mixture
  lemmas), a 5-step reviewer map, and the updated +192/−15 scope line.
- **Two OPTIONAL separate comments** (not the body — keeps the review path short):
  the supporting-material pointer and the reviewer-focus questions. Post them as PR
  comments only if you want to.
- Your **vouching sentence** (§ "AI assistance") — post as-is only if true for you.

---

## 5. After the PR is open (your actions, per §3.1)

1. **Zulip `#Physlib`**: announce the PR. Draft is in the mentormind-side `PR-TEXT.md §2`
   (also carries the separate `withDensity`/Jacobian Surfaces design question — that's a
   heads-up for a *later* submission, not this PR).
2. **Bibliography**: AI-POLICY §2.1 requires you to personally confirm the references. The
   load-bearing arXiv IDs were machine-checked 2026-07-06 (see `docs/literature.qmd §5`);
   the final human check is yours.
3. **Courtesy follow-up you can offer JTS**: `DPI.lean:36`'s header comment mis-attributes
   arXiv:1306.5920 to Leditzky–Rouzé–Datta — that eprint is **Beigi**; the real LRD paper
   is arXiv:1604.02119. Deliberately **not** bundled into this PR (keeps it single-concept);
   offer it as a trivial follow-up if he's interested.
4. **Review iteration**: expect `awaiting-author`-style back-and-forth (their norm; ~half
   the work is post-PR). If you use AI to implement his feedback, §3.2 requires you to
   verify it yourself before requesting re-review.

---

## 6. If he prefers a different factoring

The PR body already offers to relocate the theorem out of `DPI.lean` (the import-cycle
placement) and notes the supporting lemmas can be promoted to public API. Two larger
options were deliberately left as *offers* rather than baked in — a `Mixable`-native binary
convexity lemma, and sharing the `α→1⁺` transfer skeleton with the existing
`sandwichedRenyiEntropy_DPI_eq_one`. Mention them if he wants more structure; both are
described in the mentormind-side `STAGE2-REFACTOR-MENU.md`.
