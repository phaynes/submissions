# Recorded check results

Reproduce all of these with `../verify.sh <your-physlib-checkout>`. Recorded from the
`feat/qrelent-joint-convexity` branch (proof commit `a1303c7b`). A freshly generated
transcript of checks 2–4 is in [`lean-run.txt`](lean-run.txt).

| # | Check | Result |
|---|---|---|
| 1 | Statement diff vs master | **matches the original stub** after proof-body + attribute removal — no hypothesis or conclusion changed |
| 2 | `#print axioms qRelativeEnt_joint_convexity` | `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`** |
| 3 | `lake build QuantumInfo` | **green** (`Build completed successfully (8636 jobs)`) — the whole `QuantumInfo` library, which also exercises the new `@[simp] Mixable.mix_one` against every downstream user |
| 4 | `lint_all` and `scripts/lint-style.sh` | **both clean** (exit 0) for the three changed files. `lint_all` reports four pre-existing "transitive imports" flags in `Physlib/SpaceAndTime/*` — files this PR does not touch, in a library that does not import `QuantumInfo`; this PR adds no `import` lines, so those flags are independent of it |

Check 2 is the strongest: it is a property of the Lean kernel, not of any tool that
could be worked around. See
[`verification-method.md`](../../../../process/verification-method.md).

## PR size (disclosed)

`+192 / −15` = **177 net lines** across three files — the guidelines' "large PR (100–200)"
band. It is one theorem with its minimal supporting API, already factored into small
single-purpose lemmas per the repo's proof-structure guidance; it does not split
meaningfully further. Flagged honestly, not hidden.
