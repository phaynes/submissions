#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"

required=(
  "README.md"
  "DESIGN.md"
  "PLAN.md"
  "PROJECT-PLAN.md"
  "CODEX-REVIEW.md"
  "PR-BODY.md"
  "verify.sh"
  "docs/physics-brief.qmd"
  "docs/refactor-methodology.qmd"
  "evidence/checks.md"
  "evidence/build-environment.md"
  "evidence/final-validation-report.md"
  "evidence/standards-trace.md"
  "evidence/varro/equivalence-report.json"
  "evidence/review/claude-review.md"
  "proof/refactor-summary.md"
  "process/SRS.md"
  "process/traceability.md"
  "process/check-srs.sh"
  "process/yaqin-tooling-process.md"
)

missing=0
for path in "${required[@]}"; do
  if [[ ! -e "$root/$path" ]]; then
    echo "missing: $path"
    missing=$((missing + 1))
  fi
done

if [[ "$missing" -ne 0 ]]; then
  echo "submission check failed: $missing missing artifact(s)" >&2
  exit 1
fi

"$root/process/check-srs.sh"

echo "submission packet artifacts present"
