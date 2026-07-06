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

1. `p = 0` and `p = 1`;
2. support-failure cases, where the right-hand side is `⊤`;
3. the finite-support case, using joint convexity of `Q̃_α`;
4. the limit passage `α → 1⁺`.

## Declarations added / removed

| Declaration | File | Notes |
|---|---|---|
| removed `@[sorryful] qRelativeEnt_joint_convexity` | `QuantumInfo/Entropy/Relative.lean` | removes the old stub |
| `sandwichedTraceFunctional_sub_one_div_eventually_le` | `QuantumInfo/Entropy/DPI.lean` | new private helper lemma |
| `qRelativeEnt_joint_convexity` | `QuantumInfo/Entropy/DPI.lean` | proves the old theorem statement |

## Placement

The stub lived in `Relative.lean`, but the proof needs the `Q̃_α` machinery already in
`DPI.lean`. Since `DPI.lean` imports `Relative.lean`, proving this in `Relative.lean`
would create an import cycle. I therefore placed the proof in `DPI.lean`.

If maintainers prefer a different home, I am happy to move it.

## Reviewer map

Suggested review order:

1. `Relative.lean`: confirm only the old `@[sorryful]` stub was removed.
2. `DPI.lean`: review the private majorant lemma
   `sandwichedTraceFunctional_sub_one_div_eventually_le`.
3. `DPI.lean`: review `qRelativeEnt_joint_convexity`, especially:
   - degenerate weights;
   - `⊤` support-failure cases;
   - mixture kernel bookkeeping;
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

## Scope

This is a single-concept PR: it closes one open `sorry` for joint convexity of `𝐃`. The
proof is about 190 added lines, so it is in the large-PR band, but it does not split
naturally into separate PRs. The main reusable estimate is already extracted as a
private helper lemma.

## AI assistance

Developed with AI assistance. I have reviewed the theorem statement, every proof step,
and the supporting references, and I take responsibility for the submission under
`AI-POLICY.md`.
```

---

## Optional supporting-material comment

*Post this as a **separate PR comment**, not in the main body — it keeps the review path
short.*

```markdown
Optional supporting material for reviewers who want more context:

- Conventional mathematical proof: explains the Lean proof step-by-step in ordinary notation.
- Literature note: compares this `α → 1⁺` sandwiched-Rényi route with the classical
  Lindblad/Lieb route.
- Verification script: one-command check for statement match, `#print axioms`, and build.
- Evidence folder: recorded check outputs and build environment.
- Copyright note: the Lindblad 1974 PDF is not committed because it is not openly licensed.

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
4. If the statement, placement, and proof structure look acceptable, this should be
   ready after any style comments are addressed.
```
