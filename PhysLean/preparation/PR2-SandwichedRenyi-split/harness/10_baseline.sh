#!/usr/bin/env bash
# 10_baseline.sh [--axioms] — capture the pre-refactor baseline (run from ANY cwd).
#
# Artifacts land in harness/baseline/:
#   META.txt              git rev, date, file list
#   inventory.tsv         name/kind/privacy/stmt-sha/file/line for every decl in the file-set
#   inventory.names       sorted "name<TAB>kind<TAB>privacy<TAB>sha" (file-agnostic; H1/H2/H6 input)
#   sorries.txt           sorry/admit census of QuantumInfo (expect 1 known: none — see note)
#   axioms.txt            (--axioms only; needs a built env) `#print axioms` for EVERY public
#                         theorem/lemma in the file-set, sorted. Kernel-level H3 input.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
PHYSLIB="${PHYSLIB:-/Volumes/second-store/devel/knowledge-base-mcp/mentormind/physlib-contrib}"
OUT="$HERE/baseline"
mkdir -p "$OUT"
source "$HERE/lib.sh"

# The blast-radius file-set: files that move code, plus every downstream consumer of the
# cluster's public names (measured 2026-07-08 at 720c9fff).
FILES=(
  QuantumInfo/Entropy/Relative.lean
  QuantumInfo/Entropy/DPI.lean
  QuantumInfo/ClassicalInfo/Prob.lean
  QuantumInfo/Channels/Pinching.lean
  QuantumInfo/ResourceTheory/FreeState.lean
  QuantumInfo/ResourceTheory/HypothesisTesting.lean
  QuantumInfo/ResourceTheory/SteinsLemma.lean
)

cd "$PHYSLIB"
{ echo "rev: $(git rev-parse HEAD)"; echo "date: $(date -u +%Y-%m-%dT%H:%M:%SZ)";
  printf 'file: %s\n' "${FILES[@]}"; } > "$OUT/META.txt"

: > "$OUT/inventory.tsv"
for f in "${FILES[@]}"; do extract_inventory "$f" >> "$OUT/inventory.tsv"; done
cut -f1-4 "$OUT/inventory.tsv" | sort > "$OUT/inventory.names"
echo "inventory: $(wc -l < "$OUT/inventory.tsv" | tr -d ' ') declarations across ${#FILES[@]} files"

grep -rnE "\bsorry\b|\badmit\b" QuantumInfo --include="*.lean" | grep -v "sorryful\|Sorry\|-- " \
  | sort > "$OUT/sorries.txt" || true
echo "sorry/admit lines recorded: $(wc -l < "$OUT/sorries.txt" | tr -d ' ')"

if [[ "${1:-}" == "--axioms" ]]; then
  echo "capturing axiom surface (needs built env; slow on cold cache)..."
  probe=$(mktemp)
  echo "import QuantumInfo" > "$probe"
  awk -F'\t' '($2=="theorem"||$2=="lemma") && $3=="public" {print "#print axioms " $1}' \
    "$OUT/inventory.tsv" | sort -u >> "$probe"
  lake env lean "$probe" 2>&1 | grep "depends on axioms" | sort > "$OUT/axioms.txt"
  echo "axiom rows: $(wc -l < "$OUT/axioms.txt" | tr -d ' ')"
  rm -f "$probe"
else
  echo "(axiom baseline skipped — rerun with --axioms once 'lake build' is green)"
fi
echo "BASELINE CAPTURED -> $OUT"
