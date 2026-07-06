# Pull request — body

*This is the pull-request description prepared for the PhysLean maintainers. It is
written so a reviewer seeing the PR cold understands what it does, where it goes, and
how it is checked. It has **not** been posted — per PhysLean `AI-POLICY.md` §3.1, a
human opens the PR and posts to the forum.*

**Title**

```
feat(QuantumInfo): prove qRelativeEnt_joint_convexity (joint convexity of quantum relative entropy)
```

**Body**

Closes the `@[sorryful]` open `sorry` for **joint convexity of the Umegaki quantum
relative entropy**. QuantumInfo sorry count −1; none added.

For all `ρ₁ ρ₂ σ₁ σ₂ : MState d` and `p : Prob`:

    𝐃(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) ≤ p * 𝐃(ρ₁‖σ₁) + (1 - p) * 𝐃(ρ₂‖σ₂)

The statement matches the original stub (only the proof is new). The route is the
α → 1⁺ limit over machinery already in the library: joint convexity of the sandwiched
trace functional (`sandwichedTraceFunctional_jointly_convex`) plus continuity of
α ↦ D̃_α (`sandwichedRelRentropy.continuousOn`) — the same limiting pattern the library
already uses to derive the α = 1 DPI. Differentiability at α = 1 is not needed; a
one-sided convergent majorant suffices (the added private lemma below).

### Declarations added / removed

| Declaration | File | Explanation |
|---|---|---|
| `qRelativeEnt_joint_convexity` — **removed** | `QuantumInfo/Entropy/Relative.lean` | the `@[sorryful] … := by sorry` stub and its TODO comment (−15 lines) |
| `sandwichedTraceFunctional_sub_one_div_eventually_le` — **added** (`private lemma`) | `QuantumInfo/Entropy/DPI.lean` | for supp ρ ⊆ supp σ: an eventual upper bound `(Q̃_α(ρ‖σ) − 1)/(α − 1) ≤ u(α)` with `u(α) → 𝐃(ρ‖σ)` as α → 1⁺, from `log x ≤ x − 1` and `|eˣ − 1 − x| ≤ x²` |
| `qRelativeEnt_joint_convexity` — **added** (`theorem`) | `QuantumInfo/Entropy/DPI.lean` | the result; cases: degenerate weights (p ∈ {0,1}), infinite RHS (support-condition failure), main case by convexity of Q̃_α + the majorant + `le_of_tendsto_of_tendsto` |

Kept as `theorem` (not `lemma`): headline result, well known in the physics literature.
No new files.

### Placement (import cycle) — happy to relocate

The stub lived in `Relative.lean`, but the proof needs the `Q̃_α` machinery of
`DPI.lean`, which **imports** `Relative.lean` — proving it in place would create an
import cycle. It is therefore proved in `DPI.lean` (new section *Joint Convexity of the
Relative Entropy*). If you'd prefer a dedicated file or a different home, it is a
one-line move.

### Reviewer map

1. `Relative.lean` diff: the removed stub (confirm the statement moved unchanged).
2. `DPI.lean`, the majorant lemma `sandwichedTraceFunctional_sub_one_div_eventually_le`
   (short, self-contained).
3. `DPI.lean`, `qRelativeEnt_joint_convexity`: case split as in the table above.

### Checks

- `#print axioms qRelativeEnt_joint_convexity` → `[propext, Classical.choice,
  Quot.sound]` — no `sorryAx`.
- `lake build` green. Style lint: the **added lines introduce no new `ERR_LIN`**; the
  pre-existing lint in `DPI.lean` (e.g. the 127-char comment at `:266`) and in
  `Relative.lean` predates this PR and is left untouched. A fresh
  `#print axioms` / `lake build` / lint transcript is attached as `evidence/lean-run.txt`.
- PR size: +191/−15 (net 176) — in the guidelines' "large (100–200)" band. It is one
  theorem's proof; the boundary and ⊤ cases could be factored into helper lemmas if you
  prefer a smaller main body.

### AI assistance

Developed with AI assistance under `AI-POLICY.md`/`AGENTS.md`. I have reviewed every
line and certify that each statement and proof step means what it claims (§1.7); the
bibliography in the accompanying notes was verified by me per §2.1.
