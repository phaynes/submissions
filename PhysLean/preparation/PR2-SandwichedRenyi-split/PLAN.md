# Completed Execution Plan - PR2 `SandwichedRenyi.lean` Split

## Goal

Prepare a PhysLean PR that extracts the sandwiched Renyi relative entropy family
into `QuantumInfo/Entropy/SandwichedRenyi.lean`, leaves the Umegaki relative
entropy API in `QuantumInfo/Entropy/Relative.lean`, and proves that the public
surface remains stable except for reviewed, documented deltas.

## Completed Milestones

| Milestone | Result | Evidence |
|---|---|---|
| M1 baseline capture | Completed. Baseline inventory, signatures, axiom surface, and sorries captured under `harness/baseline/`. | `harness/baseline/` |
| M2 proof graph review | Completed. Lean-backed Varro queries identified the lower-semicontinuity boundary problem. | `evidence/varro/equivalence-report.json` |
| M3 first split | Completed and rejected as suboptimal because it leaked eigen-weight helpers. | `docs/refactor-methodology.qmd` |
| M4 V2 architecture | Completed. Alpha-equals-one lower-semicontinuity moved into the sandwiched file; Umegaki theorem became a stable wrapper. | `DESIGN.md` |
| M5 implementation | Completed. New file added, imports updated, `Relative.lean` reduced. | physlib checkout |
| M6 independent review | Completed. Claude review found no blocking issues before final validation. | `evidence/review/claude-review.md` |
| M7 equivalence validation | Completed. Public surface, wrapper type hash, private-helper resolution, harness, axioms, and full build passed. | `evidence/final-validation-report.md`, `evidence/varro/equivalence-report.json`, `evidence/logs/` |
| M8 submission packet | Completed. Plain-English brief, physics context, standards SRS, traceability, verifier, and PR body created. | `README.md`, `docs/`, `process/`, `PR-BODY.md`, `verify.sh` |

## Execution Sequence

1. Capture the pre-refactor baseline with `harness/10_baseline.sh`.
2. Use Varro-backed Lean queries to inspect declarations, dependency edges,
   kernel signatures, and private-name resolution.
3. Create `QuantumInfo/Entropy/SandwichedRenyi.lean` and import it from
   `QuantumInfo.lean`.
4. Move the `D̃_α` definition, notation, analytic engine, nonnegativity,
   additivity, continuity, congruence, and alpha-equals-one machinery into the
   new file.
5. Keep `qRelativeEnt` and notation `𝐃` in `Relative.lean`.
6. Replace `qRelativeEnt.lowerSemicontinuous` with a wrapper around
   `sandwichedRelRentropy_one_lowerSemicontinuous`.
7. Restore the eigen-weight helpers to private declarations in the new file.
8. Add the new file to `scripts/LinterExemption.txt` to preserve the existing
   QuantumInfo style-lint migration boundary.
9. Run the affected module builds, PR2 harness, axiom/signature checks, full
   build, style linter, SRS trace, and packet check.

## Acceptance Criteria

| Criterion | Status |
|---|---|
| `QuantumInfo.Entropy.SandwichedRenyi` builds | PASS |
| `QuantumInfo.Entropy.Relative` builds | PASS |
| Full `lake build` succeeds | PASS |
| PR2 harness passes | PASS |
| PR2 harness `--axioms` passes | PASS |
| `qRelativeEnt.lowerSemicontinuous` normalized type hash unchanged | PASS |
| Eigen-weight helpers resolve as private declarations in the new module | PASS |
| Claude review has no blocking findings | PASS |
| Submission SRS trace passes | PASS |
| Packet completeness check passes | PASS |

## Reviewer Replay

From this directory:

```bash
./verify.sh /Volumes/second-store/devel/knowledge-base-mcp/mentormind/physlib-contrib
```

For the slower complete lint gate:

```bash
LINT_ALL=1 ./verify.sh /Volumes/second-store/devel/knowledge-base-mcp/mentormind/physlib-contrib
```

## Residual Scope

The following are intentionally not part of PR2:

- style-normalizing the moved QuantumInfo proof block;
- moving general helper lemmas to `ForMathlib`;
- splitting `SandwichedRenyi.lean` into smaller follow-up files;
- renaming existing declarations;
- adding new physics results.

Those can be scheduled as follow-up PRs after this concept split is reviewed.
