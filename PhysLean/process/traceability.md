# Traceability — requirement → evidence

Each requirement in [`SRS.md`](SRS.md) traced to the artifact that satisfies it, for the
current submission (Joint convexity of the Umegaki quantum relative entropy). Paths are
relative to this `PhysLean/process/` directory. Presence of each artifact is checked by
[`check-srs.sh`](check-srs.sh); see [`srs-results.txt`](srs-results.txt).

Let `S = ../submitted/Proof-Joint-convexity-of-the-Umegaki-quantum-relative-entropy`.

| Requirement | Evidence artifact | Status |
|---|---|---|
| FR-SUB-001 Statement integrity | `S/evidence/checks.md` (check 1: byte-identical); `S/proof/qrelent-joint-convexity.patch` | ✅ met |
| FR-SUB-002 Kernel soundness | `S/evidence/checks.md` (check 2: `#print axioms`, no `sorryAx`) | ✅ met |
| FR-SUB-003 One-command repro | `S/verify.sh` | ✅ met |
| FR-SUB-004 Human-readable proof | `S/paper/joint-convexity-proof.qmd` → `S/paper/joint-convexity-proof.pdf` | ✅ met |
| FR-SUB-005 Fidelity evidence | `S/test/fidelity-check.sh` → `S/test/fidelity-results.txt` (10/10 PASS) | ✅ met |
| FR-SUB-006 Literature location | `S/test/literature-correspondence.md`; `S/docs/literature.qmd` | ✅ met |
| FR-SUB-007 Guideline traceability | `S/README.md` §5 (SRS trace to PhysLean ReviewGuidelines; PR-length disclosed) | ✅ met |
| FR-SUB-008 Build environment | `S/evidence/build-environment.md` (toolchain, revs, host, `.olean`) | ⚠️ partial — fresh transcript pending a Lean machine |
| FR-SUB-009 Reviewer PR description | `S/PR-BODY.md` | ✅ met |
| FR-SUB-010 Policy conformance | `S/PR-BODY.md` (AI-assistance certification §); repo `README.md` (human-only reviewer contact) | ✅ met |
| NFR-SUB-001 Ten-minute review | `S/README.md` (reading order); `S/PR-BODY.md` (reviewer map) | ✅ met (by construction) |
| NFR-SUB-002 Evidence honesty | citations labelled self-reported in `S/docs/literature.qmd`; QMDs band `unverified` in the tracker | ✅ met |
| NFR-SUB-003 Staging separation | repo `README.md` (“not an official submission channel”); `S/README.md` status banner | ✅ met |
| NFR-SUB-004 Self-containment | this map + `check-srs.sh` (all links resolve) | ✅ met |

## Summary

13 of 14 requirements fully met; **1 partial** (FR-SUB-008: the build *environment* and
artifact are recorded, but a freshly generated `lake build` / `#print axioms` transcript
is pending a machine with the Lean toolchain — see
`S/evidence/build-environment.md` §4). No requirement is silently passed.
