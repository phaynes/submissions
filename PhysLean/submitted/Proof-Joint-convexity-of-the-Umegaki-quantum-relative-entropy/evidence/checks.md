# Recorded check results

Reproduce all of these with `../verify.sh <your-physlib-checkout>`. Recorded from the
`feat/qrelent-joint-convexity` branch (proof commit `bb18f8dc`). A freshly generated
transcript of checks 2–4 is in [`lean-run.txt`](lean-run.txt).

| # | Check | Result |
|---|---|---|
| 1 | Statement diff vs master | **matches the original stub** after proof-body + attribute removal — no hypothesis or conclusion changed |
| 2 | `#print axioms qRelativeEnt_joint_convexity` | `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`** |
| 3 | `lake build` of the module | **green** (`Build completed successfully`) |
| 4 | `lint-style.py` on the two changed files | the **added lines introduce no new `ERR_LIN`**; the pre-existing lint debt in `DPI.lean` (e.g. `:266`) and `Relative.lean` is left untouched and is out of scope |

Check 2 is the strongest: it is a property of the Lean kernel, not of any tool that
could be worked around. See
[`verification-method.md`](../../../../process/verification-method.md).

## PR size (disclosed)

`+191 / −15` = **176 net lines** — the guidelines' "large PR (100–200)" band. It is one
theorem's proof and does not split meaningfully; the boundary/⊤ cases could be factored
into helper lemmas on request. Flagged honestly, not hidden.
