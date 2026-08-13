# PR2 Requirement Traceability

| Requirement | Evidence | Status |
|---|---|---|
| FR-PR2-001 concept boundary | `README.md`, `DESIGN.md`, `docs/refactor-methodology.qmd`, `proof/refactor-summary.md`, `QuantumInfo/Entropy/SandwichedRenyi.lean`, `QuantumInfo/Entropy/Relative.lean` | met |
| FR-PR2-002 statement preservation | `harness/20_check.sh --axioms`, `evidence/varro/equivalence-report.json`, `evidence/final-validation-report.md` | met |
| FR-PR2-003 wrapper equivalence | `evidence/varro/equivalence-report.json`: normalized type hashes for `qRelativeEnt.lowerSemicontinuous` match | met |
| FR-PR2-004 privacy restoration | `evidence/varro/equivalence-report.json`: eigen-weight helpers resolve as `_private...SandwichedRenyi...` | met |
| FR-PR2-005 import acyclicity | `evidence/review/claude-review.md`, successful full `lake build` | met |
| FR-PR2-006 kernel validation | `evidence/logs/lake-build-*.log`, `evidence/logs/pr2-harness*.log` | met |
| FR-PR2-007 standards conformance | `scripts/LinterExemption.txt`, `evidence/logs/lint-style-sh.log`, `evidence/logs/lint-style-exemption-check.log`, `evidence/logs/lint-all.log`, `evidence/standards-trace.md` | met with disclosed exemption and repo-external `lint_all` caveat |
| FR-PR2-008 reviewer packet | `README.md`, `DESIGN.md`, `PLAN.md`, `PROJECT-PLAN.md`, `CODEX-REVIEW.md`, `PR-BODY.md`, `docs/`, `evidence/`, `proof/`, `process/yaqin-tooling-process.md`, `verify.sh` | met |
| FR-PR2-009 AI policy disclosure | `PR-BODY.md` | met |
| NFR-PR2-001 evidence first | All validation claims cite packet evidence | met |
| NFR-PR2-002 single-concept scope | `README.md` scope limits; no theorem renames or proof-golf claimed | met |
| NFR-PR2-003 reviewer speed | `README.md` reviewer summary and reviewer map | met |
| NFR-PR2-004 reproducibility | `verify.sh`, `evidence/replay-commands.sh` | met |

## Standards Trace

| Source requirement | PR2 response |
|---|---|
| Correct abstraction of lemmas and definitions | `D̃_α` family now owns its analytic proof machinery; `𝐃` remains the Umegaki wrapper. |
| Correct type-theory use | `qRelativeEnt` remains definitionally `D̃_1`; wrapper equivalence is checked by normalized Lean type hash. |
| Do not reprove existing Mathlib/PhysLean facts | No new mathematical theorem is introduced beyond the boundary theorem needed for ownership; proof bodies are moved, not re-proved. |
| Concise proofs where possible | This PR does not rewrite proofs; it avoids proof-golf in a move PR. Long inherited proofs are preserved and isolated in the concept file. |
| Correct file placement | `SandwichedRenyi.lean` owns sandwiched Renyi definitions and API; `Relative.lean` owns Umegaki names. |
| New files suitably named and located | `QuantumInfo/Entropy/SandwichedRenyi.lean` follows sibling entropy-file naming (`VonNeumann`, `Relative`, `DPI`, `SSA`). |
| Sufficient documentation | Packet supplies README, PR body, physics brief, and methodology brief. |
| Prefer `lemma` over `theorem` except important results | Existing declarations are preserved; the new public boundary theorem is important API for `D̃_1` lower semicontinuity. |
| Single coherent PR concept | Scope is the sandwiched Renyi split and ownership correction. |
| `lake exe lint_all` and `lint-style.sh` | `lint-style.sh` passes; `SandwichedRenyi.lean` is explicitly listed in `scripts/LinterExemption.txt` because it moves currently exempt QuantumInfo code. |
| AI policy | PR body discloses AI assistance and human responsibility. |
