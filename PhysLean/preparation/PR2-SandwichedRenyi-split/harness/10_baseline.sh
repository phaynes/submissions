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

# B1 SELF-TEST (Codex): confirm notation commands did NOT swallow adjacent declarations.
# These three straddle notation commands in Relative.lean; all must be present.
for must in qRelativeEnt SandwichedRelRentropy sandwichedRelRentropy_additive_alpha_one; do
  awk -F'\t' -v n="$must" '$1==n{found=1} END{exit !found}' "$OUT/inventory.tsv" \
    || { echo "SELF-TEST FAIL: '$must' missing — extractor regressed (notation swallow?)"; exit 4; }
done
echo "self-test: extractor OK (notation not swallowing)"

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

  echo "capturing kernel signature baseline (Codex B4)..."
  cp "$HERE/sig_check.lean" "$PHYSLIB/sig_check.lean"
  awk -F'\t' '$3=="public"{print $1}' "$OUT/inventory.tsv" | sort -u > "$PHYSLIB/sig_names.txt"
  ( cd "$PHYSLIB" && lake env lean --run sig_check.lean 2>/dev/null ) \
    | sed -E 's/_@\.[A-Za-z0-9_.]*_hyg[A-Za-z0-9._]*/_HYG_/g' \
    | while IFS= read -r rec; do
        n=$(printf '%s' "$rec" | cut -d' ' -f1)
        h=$(printf '%s' "$rec" | shasum -a 256 | cut -c1-16)
        printf '%s\t%s\n' "$h" "$n"
      done | sort -k2 > "$OUT/sig.hashes"
  rm -f "$PHYSLIB/sig_check.lean" "$PHYSLIB/sig_names.txt"
  echo "signature rows: $(wc -l < "$OUT/sig.hashes" | tr -d ' ')"
else
  echo "(axiom baseline skipped — rerun with --axioms once 'lake build' is green)"
fi
echo "BASELINE CAPTURED -> $OUT"
