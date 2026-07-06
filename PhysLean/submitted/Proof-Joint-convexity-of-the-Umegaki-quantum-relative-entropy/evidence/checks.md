# Recorded check results

Reproduce all of these with `../verify.sh <your-physlib-checkout>`. Recorded from the
`feat/qrelent-joint-convexity` branch (proof commit `9385c7f3`). A freshly generated
transcript of checks 2–4 is in [`lean-run.txt`](lean-run.txt).

| # | Check | Result |
|---|---|---|
| 1 | Statement diff vs master | **matches the original stub** after proof-body + attribute removal — no hypothesis or conclusion changed |
| 2 | `#print axioms qRelativeEnt_joint_convexity` | `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`** |
| 3 | `lake build QuantumInfo.Entropy.DPI` | **green** (`Build completed successfully`) — the changed module, not the whole library |
| 4 | `lint_all` and `scripts/lint-style.sh` | **both clean** (exit 0). The two changed files are on the upstream `LinterExemption.txt`, so `lint-style.sh` does not style-lint them today; run directly with `lint-style.py`, the added lines still add no new `ERR_LIN` |

Check 2 is the strongest: it is a property of the Lean kernel, not of any tool that
could be worked around. See
[`verification-method.md`](../../../../process/verification-method.md).

## PR size (disclosed)

`+186 / −15` = **171 net lines** — the guidelines' "large PR (100–200)" band. It is one
theorem's proof and does not split meaningfully; the boundary/⊤ cases could be factored
into helper lemmas on request. Flagged honestly, not hidden.
