#!/usr/bin/env bash
set -euo pipefail

ROOT="${ROOT:-/Volumes/second-store/devel/knowledge-base-mcp/mentormind}"
PHYSLIB="${PHYSLIB:-$ROOT/physlib-contrib}"
KG="${KG:-$ROOT/helios-projects/project/knowledge-graphs}"
LRA="${LRA:-$ROOT/helios-projects/project/yaqin}"
HARNESS="${HARNESS:-/Volumes/second-store/devel/knowledge-base-mcp/submissions/PhysLean/preparation/PR2-SandwichedRenyi-split/harness}"
VARRO="${VARRO:-$KG/target/debug/varro}"
FINAL="$LRA/evidence/pr2-v2/final"

mkdir -p "$FINAL"

echo "== Varro V2 module and declaration facts =="
export VARRO_LEAN_TARGET_CHECKOUT="$PHYSLIB"
"$VARRO" show lean module QuantumInfo.Entropy.SandwichedRenyi
"$VARRO" show lean module QuantumInfo.Entropy.Relative
"$VARRO" show lean declaration qRelativeEnt.lowerSemicontinuous
"$VARRO" show lean declaration sandwichedRelRentropy_one_lowerSemicontinuous
"$VARRO" show lean declaration eigenWeight
"$VARRO" show lean declaration inner_cfc_eq_sum_eigenWeight
"$VARRO" show lean declaration eigenWeight_nonneg
"$VARRO" show lean declaration eigenWeight_zero_of_eigenvalue_zero

echo "== Lean module builds =="
(
  cd "$PHYSLIB"
  lake build QuantumInfo.Entropy.SandwichedRenyi
  lake build QuantumInfo.Entropy.Relative
)

echo "== PR2 harness =="
"$HARNESS/20_check.sh"
"$HARNESS/20_check.sh" --axioms

echo "== Full lake build =="
(
  cd "$PHYSLIB"
  lake build
)

echo "== Captured summary =="
sed -n '1,220p' "$FINAL/final-validation-report.md"
