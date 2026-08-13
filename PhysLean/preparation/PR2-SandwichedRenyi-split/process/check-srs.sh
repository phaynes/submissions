#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/.." && pwd)"
out="$here/srs-results.txt"

rows=(
  "FR-PR2-001|README.md|met"
  "FR-PR2-001|DESIGN.md|met"
  "FR-PR2-001|docs/refactor-methodology.qmd|met"
  "FR-PR2-001|proof/refactor-summary.md|met"
  "FR-PR2-002|evidence/varro/equivalence-report.json|met"
  "FR-PR2-002|evidence/logs/pr2-harness-axioms.log|met"
  "FR-PR2-003|evidence/varro/equivalence-report.json|met"
  "FR-PR2-004|evidence/varro/equivalence-report.json|met"
  "FR-PR2-005|evidence/review/claude-review.md|met"
  "FR-PR2-006|evidence/logs/lake-build-full.log|met"
  "FR-PR2-006|evidence/logs/pr2-harness.log|met"
  "FR-PR2-007|evidence/standards-trace.md|met"
  "FR-PR2-008|PR-BODY.md|met"
  "FR-PR2-008|PLAN.md|met"
  "FR-PR2-008|PROJECT-PLAN.md|met"
  "FR-PR2-008|CODEX-REVIEW.md|met"
  "FR-PR2-008|docs/physics-brief.qmd|met"
  "FR-PR2-008|process/yaqin-tooling-process.md|met"
  "FR-PR2-009|PR-BODY.md|met"
  "NFR-PR2-004|verify.sh|met"
)

pass=0
missing=0

{
  echo "PR2 SRS trace check"
  echo
  printf "%-13s %-8s %-6s %s\n" "requirement" "status" "file?" "artifact"
  printf '%.0s-' {1..78}
  echo
  for row in "${rows[@]}"; do
    IFS='|' read -r req artifact status <<< "$row"
    if [[ -e "$root/$artifact" ]]; then
      exists=yes
      pass=$((pass + 1))
    else
      exists=NO
      status=MISSING
      missing=$((missing + 1))
    fi
    printf "%-13s %-8s %-6s %s\n" "$req" "$status" "$exists" "$artifact"
  done
  echo
  echo "artifacts present: $pass"
  echo "missing: $missing"
  if [[ "$missing" -eq 0 ]]; then
    echo "RESULT: PASS"
  else
    echo "RESULT: FAIL"
  fi
} | tee "$out"

[[ "$missing" -eq 0 ]]
