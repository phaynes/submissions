# Recorded check results

Reproduce all of these with `../verify.sh <your-physlib-checkout>`. Recorded from the
`feat/qrelent-joint-convexity` branch (proof commit `bb18f8dc`).

| # | Check | Result |
|---|---|---|
| 1 | Statement diff vs master | **byte-identical** — only the proof is new |
| 2 | `#print axioms qRelativeEnt_joint_convexity` | `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`** |
| 3 | `lake build` of the module | **green** (full library builds) |
| 4 | `lint_all` / `lint-style` | **zero new** `ERR_LIN`; one pre-existing long line (`DPI.lean:266`) already on master, unrelated |

Check 2 is decisive: it is a property of the Lean kernel and cannot be gamed. See
[`verification-method.md`](../../../../process/verification-method.md).

## PR size (disclosed)

`+191 / −15` = **176 net lines** — the guidelines' "large PR (100–200)" band. It is one
theorem's proof and does not split meaningfully; the boundary/⊤ cases could be factored
into helper lemmas on request. Flagged honestly, not hidden.
