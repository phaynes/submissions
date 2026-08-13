#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
PHYSLIB="${1:-/Volumes/second-store/devel/knowledge-base-mcp/mentormind/physlib-contrib}"
HARNESS="$here/harness"

if [[ ! -d "$PHYSLIB" ]]; then
  echo "physlib checkout not found: $PHYSLIB" >&2
  exit 2
fi

echo "== affected module builds =="
(
  cd "$PHYSLIB"
  lake build QuantumInfo.Entropy.SandwichedRenyi
  lake build QuantumInfo.Entropy.Relative
)

echo "== PR2 harness =="
PHYSLIB="$PHYSLIB" "$HARNESS/20_check.sh"
PHYSLIB="$PHYSLIB" "$HARNESS/20_check.sh" --axioms

echo "== full lake build =="
(
  cd "$PHYSLIB"
  lake build
)

echo "== style linter =="
(
  cd "$PHYSLIB"
  ./scripts/lint-style.sh
)

if [[ "${LINT_ALL:-0}" == "1" ]]; then
  echo "== lint_all =="
  (
    cd "$PHYSLIB"
    lake exe lint_all
  )
else
  echo "== lint_all skipped =="
  echo "Set LINT_ALL=1 to run lake exe lint_all."
fi

echo "== SRS trace =="
"$here/process/check-srs.sh"

echo "ALL PR2 SUBMISSION CHECKS PASSED"
