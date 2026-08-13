# Pull request — body

*This is the pull-request description prepared for the PhysLean maintainers. It is
written so a reviewer seeing the PR cold understands what it does, where it goes, and
how it is checked. It has **not** been posted — per PhysLean `AI-POLICY.md`, a human
opens the PR and posts to the forum. The two comment blocks at the end are intended as
**separate PR comments**, not part of the body, so the main review path stays short.*

**Title**

```text
feat(QuantumInfo): prove qRelativeEnt_joint_convexity
```

**Body**

```markdown
Closes the `@[sorryful]` stub for joint convexity of the Umegaki quantum relative entropy.

For `ρ₁ ρ₂ σ₁ σ₂ : MState d` and `p : Prob`, this proves:

    𝐃(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂])
      ≤ p * 𝐃(ρ₁‖σ₁) + (1 - p) * 𝐃(ρ₂‖σ₂)

The theorem statement matches the original stub; only the proof is new.

## Proof idea

The proof uses the existing joint convexity of the sandwiched trace functional `Q̃_α`
for `α > 1`, then passes to the `α → 1⁺` limit using
`sandwichedRelRentropy.continuousOn`.

The only new analytic estimate is the private helper lemma

    sandwichedTraceFunctional_sub_one_div_eventually_le

which gives an eventual upper bound for

    (Q̃_α(ρ‖σ) - 1) / (α - 1)

by a real-valued majorant tending to `𝐃(ρ‖σ).toReal`. This avoids proving
differentiability at `α = 1`; continuity of `D̃_α`, `log x ≤ x - 1`, and the standard
bound on `exp x - 1 - x` are enough.

The main theorem then handles:

1. `p = 0` and `p = 1` (each closes by `simp`, via `mix_zero` / `mix_one`);
2. support-failure cases, where the right-hand side is `⊤` (via `qRelativeEnt_eq_top_iff`);
3. the finite-support case, using joint convexity of `Q̃_α`
   (`sandwichedTraceFunctional_mix_le`, the binary specialisation);
4. the limit passage `α → 1⁺` (`sandwichedRelRentropy_tendsto_qRelativeEnt`).

The mixture bookkeeping (`Fin 2` weighted sums, kernel inclusion) is factored into small
`private` lemmas so the main theorem reads as the four steps above.

## Declarations added / removed

| Declaration | File | Notes |
|---|---|---|
| removed `@[sorryful] qRelativeEnt_joint_convexity` | `QuantumInfo/Entropy/Relative.lean` | removes the old stub |
| `Mixable.mix_one` | `QuantumInfo/ClassicalInfo/Prob.lean` | `@[simp]`; the `p = 1` partner of the existing `@[simp] mix_zero` |
| `qRelativeEnt_ne_top_iff`, `qRelativeEnt_eq_top_iff` | `QuantumInfo/Entropy/Relative.lean` | finiteness ⇔ support condition; small API next to `qRelativeEnt_ker` |
| `sandwichedRelRentropy_tendsto_qRelativeEnt` | `QuantumInfo/Entropy/DPI.lean` | public `theorem`; `D̃_α → 𝐃` as `α → 1⁺` |
| `sandwichedTraceFunctional_sub_one_div_eventually_le` | `QuantumInfo/Entropy/DPI.lean` | private; the majorant estimate |
| `mix_M_eq_weighted_sum`, `ker_mix_le`, `sandwichedTraceFunctional_mix_le` | `QuantumInfo/Entropy/DPI.lean` | private; binary-mixture plumbing over `Fin 2` |
| `qRelativeEnt_joint_convexity` | `QuantumInfo/Entropy/DPI.lean` | proves the old theorem statement |

## Placement

The stub lived in `Relative.lean`, but the proof needs the `Q̃_α` machinery already in
`DPI.lean`. Since `DPI.lean` imports `Relative.lean`, proving this in `Relative.lean`
would create an import cycle. I therefore placed the proof in `DPI.lean`.

## Reviewer map

Suggested review order:

1. `Prob.lean`: `Mixable.mix_one` (mirrors `mix_zero` directly above it).
2. `Relative.lean`: confirm the old `@[sorryful]` stub was removed, and skim the two
   `qRelativeEnt_*_top_iff` finiteness lemmas.
3. `DPI.lean`: the continuity lemma and the private majorant lemma
   `sandwichedTraceFunctional_sub_one_div_eventually_le`.
4. `DPI.lean`: the three mixture lemmas (mechanical plumbing).
5. `DPI.lean`: review `qRelativeEnt_joint_convexity`, especially:
   - degenerate weights;
   - `⊤` support-failure cases;
   - pointwise `α > 1` bound;
   - final `le_of_tendsto_of_tendsto` step.

## Checks

Run:

```bash
lake build QuantumInfo.Entropy.DPI
echo 'import QuantumInfo.Entropy.DPI
#print axioms qRelativeEnt_joint_convexity' > /tmp/qrelent_axioms.lean
lake env lean /tmp/qrelent_axioms.lean
lake exe lint_all
./scripts/lint-style.sh
```

Expected axiom output:

```text
qRelativeEnt_joint_convexity depends on axioms:
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`.

The packet also ships a one-command verifier (`verify.sh`) that runs the statement
check plus the above. It compares the statement against `origin/master` by default; if
your base remote is not `origin`, run it as
`BASE_REF=<your-master-remote>/master ./verify.sh <physlib-checkout>`.

## Scope

This is a single-concept PR: it closes one open `sorry` for joint convexity of `𝐃`. The
change is +206/−15 (three files), so it is in the large-PR band, but it does not split
naturally into separate PRs. The supporting reasoning is already factored into small
single-purpose lemmas, and the one genuinely reusable analytic estimate is a private
helper lemma.

## AI assistance

Developed with AI assistance. I have reviewed the theorem statement, every proof step,
and the supporting references, and I take responsibility for the submission under
`AI-POLICY.md`.

## Supporting material (optional)

A self-contained review packet — conventional-maths write-up, a one-command verifier,
recorded evidence, and paper↔Lean fidelity checks — is public at
<https://github.com/phaynes/submissions/tree/qrelent-pr-v1/PhysLean/submitted/Proof-Joint-convexity-of-the-Umegaki-quantum-relative-entropy>.
It is optional context; the intended review path is the code diff and the Lean checks
above.
```

---

## Optional supporting-material comment

*Post this as a **separate PR comment**, not in the main body — it keeps the review path
short.*

```markdown
Optional supporting material for reviewers who want more context — a public, self-contained
packet (pinned to a commit so it matches this PR):
https://github.com/phaynes/submissions/tree/qrelent-pr-v1/PhysLean/submitted/Proof-Joint-convexity-of-the-Umegaki-quantum-relative-entropy

- Conventional mathematical proof (Lean → ordinary notation), with a Lean↔paper dictionary:
  paper/joint-convexity-proof.pdf and docs/proof-conventional.pdf
- Literature note comparing this α → 1⁺ sandwiched-Rényi route with the classical
  Lindblad/Lieb route: docs/literature.pdf
- One-command verifier (statement match, #print axioms, build): verify.sh
- Recorded check outputs, build environment, and the exact patch: evidence/ and proof/
- Paper↔Lean fidelity + source-consistency checks: test/

These files are not required reading for the PR. The intended review path is the code diff,
the private majorant lemma, the main theorem, and the Lean checks.
```

## Optional reviewer-focus comment

*Use only if you want to make the merge path explicit without sounding pushy.*

```markdown
Requested review focus:

1. Is `DPI.lean` the acceptable home for this theorem, given the import cycle with
   `Relative.lean`?
2. Is the private majorant lemma the right abstraction level, or would you prefer one
   more helper lemma extracted from the main theorem?
3. Are the `⊤` cases and `ENNReal.ofReal` conversions clear enough as written?
4. I would especially appreciate guidance on placement and factoring; I am happy to adjust either.
```
