# PR2 Project Plan and Completion Record

## Objective

Use Varro-backed Lean queries to support a reviewer-ready refactor of the
PhysLean sandwiched Renyi relative entropy material, then package the submission
with plain-English methodology, physics context, standards requirements, and
traceable evidence.

The architecture correction remains central: this is not a batch JSON extraction
workflow. Varro asks Lean precise questions; Lean is the authority; JSON appears
only as protocol, cache, fixture, or review evidence.

## Completed PR2 Slice

| Milestone | Outcome | Evidence |
|---|---|---|
| M1 Baseline | Captured pre-refactor declaration inventory, signatures, axiom surface, and sorries. | `harness/baseline/` |
| M2 Lean query path | Used Varro-backed Lean queries to inspect declarations, modules, dependency edges, type hashes, and private-name resolution. | `evidence/varro/equivalence-report.json`, `evidence/replay-commands.sh` |
| M3 Proof graph analysis | Identified that keeping alpha-equals-one lower-semicontinuity in `Relative.lean` would leak eigen-weight internals. | `docs/refactor-methodology.qmd` |
| M4 V2 design | Moved alpha-equals-one lower-semicontinuity proof ownership into `SandwichedRenyi.lean`; kept Umegaki API as wrapper. | `DESIGN.md` |
| M5 Code refactor | Added `QuantumInfo/Entropy/SandwichedRenyi.lean`, reduced `Relative.lean`, updated imports, restored private helpers. | physlib checkout |
| M6 Agent-callable evidence | Preserved commands and structured outputs so Codex or Claude can call the query path and use Lean facts during review/refactoring rather than relying on `awk`/`grep`. | `evidence/replay-commands.sh`, `evidence/varro/equivalence-report.json` |
| M7 Independent review | Claude reviewed the V2 refactor before final validation and reported no blocking findings. | `evidence/review/claude-review.md` |
| M8 Validation and packet | Ran module builds, full build, PR2 harness, axiom/signature checks, linter gate, SRS trace, and packet completeness check. | `evidence/final-validation-report.md`, `evidence/logs/`, `process/`, `verify.sh` |

## Agent-Callable Integration

Milestone M6 is intentionally practical rather than ornamental. The integration
needed for PR2 is:

1. A Lean query path invoked through Varro from the built physlib checkout.
2. Query outputs that expose facts useful to an AI assistant:
   declaration placement, dependency edges, public surface drift, type hashes,
   private-name resolution, and reviewed deltas.
3. Replay commands that let Codex or Claude re-ask the same Lean-backed
   questions while refactoring or reviewing.
4. Review evidence that records the query results without making the JSON files
   the source of truth.

This reduces reliance on brittle text scraping. The shell harness still exists
as an outer guardrail, but the design decision and equivalence analysis are
grounded in compiled Lean facts.

## What the PR2 Slice Does Not Claim

The completed PR2 slice does not claim to have built:

- a warm long-lived Lean daemon;
- a polished Varro UI;
- corpus-wide signature search;
- automated proof search;
- full replacement of every existing harness script.

Those are follow-up Helios/Varro product milestones. PR2 proves the useful
vertical slice: Lean-backed facts can guide and validate a real PhysLean
refactor, and the resulting evidence can be made reviewer-readable.

## Completion Gates

| Gate | Status |
|---|---|
| Varro/Lean equivalence report has `status: pass` | PASS |
| Public surface drift matches expected drift | PASS |
| `qRelativeEnt.lowerSemicontinuous` normalized type hash unchanged | PASS |
| Eigen-weight helpers resolve as private names in the new module | PASS |
| `lake build QuantumInfo.Entropy.SandwichedRenyi` | PASS |
| `lake build QuantumInfo.Entropy.Relative` | PASS |
| `harness/20_check.sh` | PASS |
| `harness/20_check.sh --axioms` | PASS |
| full `lake build` | PASS |
| `./scripts/lint-style.sh` | PASS |
| submission SRS trace | PASS |
| submission packet completeness | PASS |

## Follow-Up Product Milestones

These are useful after PR2 but intentionally outside the PR2 submission:

| Future milestone | Purpose |
|---|---|
| First-class Varro `LeanResolved` resolver | Make Lean-backed facts a stable Varro resolver with trust tags, caching, errors, and source refs. |
| Warm query process | Avoid cold-start latency once interactive proof/refactor sessions need it. |
| Dependency visualization | Render proof graph and partition checks from live Lean query output. |
| Signature discovery | Search structurally similar theorem/type signatures across the corpus. |
| Proof-support queries | Prototype goal-neighborhood and lemma-candidate queries through `MetaM`. |

The current packet should be used as the reference implementation of the
methodology: query Lean, refactor with the proof graph in view, review with an
independent assistant, and validate with kernel-level checks.
