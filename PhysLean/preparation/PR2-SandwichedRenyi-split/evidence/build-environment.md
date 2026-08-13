# Build Environment

Recorded for the PR2 V2 refactor preparation packet.

| Item | Value |
|---|---|
| Physlib checkout | `/Volumes/second-store/devel/knowledge-base-mcp/mentormind/physlib-contrib` |
| Submission packet | `/Volumes/second-store/devel/knowledge-base-mcp/submissions/PhysLean/preparation/PR2-SandwichedRenyi-split` |
| Lean | `Lean 4.31.0` (`x86_64-apple-darwin24.6.0`, commit `68218e876d2a38b1985b8590fff244a83c321783`) |
| Lake | `5.0.0-src+68218e8` |
| Physlib commit | `720c9fffe5549c9dfbbb893cc3ca37305fc6536d` |
| Lean evidence source | Varro-backed Lean query binary plus `lake build` |
| Task record | `fg-pr2-submission-brief-perfect-20260709` |

## Local PR2 checkout state

At final validation, the PR2-relevant physlib checkout state was:

```text
 M QuantumInfo.lean
 M QuantumInfo/Entropy/Relative.lean
 M scripts/LinterExemption.txt
?? QuantumInfo/Entropy/SandwichedRenyi.lean
```

The authoritative verification artifacts are in:

- `evidence/logs/`
- `evidence/varro/equivalence-report.json`
- `evidence/final-validation-report.md`

Regenerate environment details with:

```bash
cd /Volumes/second-store/devel/knowledge-base-mcp/mentormind/physlib-contrib
lake env lean --version
lake --version
git rev-parse HEAD
git status --short
```
