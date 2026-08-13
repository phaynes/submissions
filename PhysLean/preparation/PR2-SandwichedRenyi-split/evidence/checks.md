# Recorded Check Results

These results are for the PR2 V2 refactor. Reproduce with:

```bash
./verify.sh /Volumes/second-store/devel/knowledge-base-mcp/mentormind/physlib-contrib
```

## Summary

| Check | Result | Evidence |
|---|---|---|
| Claude review gate | PASS | `evidence/review/claude-review.md` |
| Varro V1-to-V2 equivalence | PASS | `evidence/varro/equivalence-report.json` |
| `qRelativeEnt.lowerSemicontinuous` statement unchanged | PASS | same normalized type hash before/after |
| Private helper restoration | PASS | eigen-weight helpers resolve as `_private...SandwichedRenyi...` |
| `lake build QuantumInfo.Entropy.SandwichedRenyi` | PASS | `evidence/logs/lake-build-sandwichedrenyi.log` |
| `lake build QuantumInfo.Entropy.Relative` | PASS | `evidence/logs/lake-build-relative.log` |
| PR2 harness | PASS | `evidence/logs/pr2-harness.log` |
| PR2 harness with axioms/signatures | PASS | `evidence/logs/pr2-harness-axioms.log` |
| full `lake build` | PASS | `evidence/logs/lake-build-full.log` |
| `./scripts/lint-style.sh` | PASS | `evidence/logs/lint-style-sh.log` |
| `lake exe lint_all` | REPO-EXTERNAL FAIL | `evidence/logs/lint-all.log` reports existing style failures in unrelated `Physlib/...` files; no PR2 `QuantumInfo` files are reported. |
| New-file style exemption | PASS | `evidence/logs/lint-style-exemption-check.log` confirms `QuantumInfo/Entropy/SandwichedRenyi.lean` is in `scripts/LinterExemption.txt`. |
| Documentation render | PASS | `evidence/logs/render-docs.log`; rendered `docs/physics-brief.html` and `docs/refactor-methodology.html`. |
| Submission packet completeness | PASS | `test/check-submission.sh`; SRS trace reports 19 artifacts present. |

## Notes

The full build emitted one unrelated pre-existing warning:

```text
Physlib/Electromagnetism/Kinematics/EMPotential.lean:284:10:
This simp argument is unused: Lorentz.Vector.smul_add
```

The new `SandwichedRenyi.lean` file is listed in `scripts/LinterExemption.txt`.
That is intentional: this PR moves code out of the already-exempt
`Relative.lean` and does not attempt a full style-normalization of inherited
QuantumInfo proof code.

`lake exe lint_all` was attempted and captured in `evidence/logs/lint-all.log`.
It reports repository-wide style failures in unrelated `Physlib/...` files. A
search of that log found no `QuantumInfo`, `SandwichedRenyi`, `Relative.lean`,
or `QuantumInfo.lean` failures. The process remained idle after emitting those
failures and was interrupted; this is recorded as a repo-external lint state,
not as a PR2 semantic or build failure.
