#!/usr/bin/env bash
# 00_manifest.sh — emit the mechanical move-manifest for HUMAN REVIEW (phase P1).
# Every declaration in Relative.lean/DPI.lean with a MOVE/STAY suggestion:
#   MOVE if the name matches the cluster pattern OR its line falls in a measured cluster range.
# Review the output, fix misclassifications, commit as manifest.reviewed.tsv.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"; source "$HERE/lib.sh"
PHYSLIB="${PHYSLIB:-/Volumes/second-store/devel/knowledge-base-mcp/mentormind/physlib-contrib}"
cd "$PHYSLIB"
suggest() { # name line file
  local n="$1" l="$2" f="$3"
  if [[ "$f" == *DPI.lean ]]; then
    [[ "$n" == sandwichedRelRentropy_tendsto_qRelativeEnt ]] && echo MOVE || echo STAY; return
  fi
  case "$n" in
    *[sS]andwiched*|notation:D̃_*|eigenWeight*|B_of*|weighted_jensen*|doubly_stochastic*) echo MOVE; return ;;
    qRelativeEnt*|notation:𝐃*) echo STAY; return ;;
  esac
  if (( l>=26 && l<=1180 )) || (( l>=1462 && l<=1495 )) || (( l>=1646 && l<=1780 )); then echo MOVE
  else echo STAY; fi
}
printf 'suggest\tname\tkind\tprivacy\tfile\tline\n'
for f in QuantumInfo/Entropy/Relative.lean QuantumInfo/Entropy/DPI.lean; do
  extract_inventory "$f" | while IFS=$'\t' read -r name kind priv sha file line; do
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$(suggest "$name" "$line" "$file")" "$name" "$kind" "$priv" "$file" "$line"
  done
done
