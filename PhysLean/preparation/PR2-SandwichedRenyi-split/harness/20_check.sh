#!/usr/bin/env bash
# 20_check.sh [--axioms] — post-refactor verification against harness/baseline/.
# Exit 0 iff every check passes. Run after EVERY phase (cheap without --axioms; with it at P8).
#
# Checks (see PLAN.md §4):
#   H1 inventory  — declaration set unchanged, modulo whitelisted additions/removals
#   H2 fidelity   — every surviving declaration's STATEMENT hash unchanged (file-agnostic)
#   H6 privacy    — privacy flag unchanged, modulo whitelisted promotions
#   H5 diff-shape — only whitelisted files differ from the baseline rev
#   H3 axioms     — (--axioms) kernel #print axioms identical for all public thms in the set
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
PHYSLIB="${PHYSLIB:-/Volumes/second-store/devel/knowledge-base-mcp/mentormind/physlib-contrib}"
BASE="$HERE/baseline"; ALLOW="$HERE/allowed-changes.txt"
source "$HERE/lib.sh"
[[ -f "$BASE/inventory.names" ]] || { echo "FATAL: no baseline — run 10_baseline.sh first"; exit 2; }
fail=0
ok()   { printf '  \033[32mPASS\033[0m %s\n' "$1"; }
bad()  { printf '  \033[31mFAIL\033[0m %s\n' "$1"; fail=1; }

# file-set = baseline files + any 'newfile' lines from the whitelist
FILES=(); while IFS= read -r l; do FILES+=("$l"); done < <(grep '^file: ' "$BASE/META.txt" | sed 's/^file: //')
NEWF=();  while IFS= read -r l; do NEWF+=("$l");  done < <(grep -E '^newfile ' "$ALLOW" 2>/dev/null | awk '{print $2}')
ALLOW_ADD=$(grep -E '^add '     "$ALLOW" 2>/dev/null | awk '{print $2}' | sort -u) || true
ALLOW_DEL=$(grep -E '^remove '  "$ALLOW" 2>/dev/null | awk '{print $2}' | sort -u) || true
ALLOW_PRO=$(grep -E '^promote ' "$ALLOW" 2>/dev/null | awk '{print $2}' | sort -u) || true
ALLOW_FILES=(); while IFS= read -r l; do ALLOW_FILES+=("$l"); done < <({ grep -E '^allow-file ' "$ALLOW" 2>/dev/null | awk '{print $2}'; printf '%s\n' "${NEWF[@]:-}"; } | sort -u)

cd "$PHYSLIB"
cur=$(mktemp)
for f in "${FILES[@]}" "${NEWF[@]:-}"; do [[ -f "$f" ]] && extract_inventory "$f"; done > "$cur.tsv"
cut -f1-4 "$cur.tsv" | sort > "$cur"

echo "== H1 inventory (set equality modulo whitelist) =="
added=$(comm -13 <(cut -f1 "$BASE/inventory.names" | sort -u) <(cut -f1 "$cur" | sort -u))
removed=$(comm -23 <(cut -f1 "$BASE/inventory.names" | sort -u) <(cut -f1 "$cur" | sort -u))
bad_add=$(comm -23 <(printf '%s\n' $added | sort -u) <(printf '%s\n' $ALLOW_ADD)) || true
bad_del=$(comm -23 <(printf '%s\n' $removed | sort -u) <(printf '%s\n' $ALLOW_DEL)) || true
[[ -z "$bad_add" ]] && ok "no unwhitelisted additions" || bad "UNWHITELISTED additions: $bad_add"
[[ -z "$bad_del" ]] && ok "no unwhitelisted removals"  || bad "UNWHITELISTED removals (LOST DECLS?): $bad_del"

echo "== H2 statement fidelity (hash per decl, file-agnostic) =="
drift=$(join -t$'\t' -j1 \
    <(awk -F'\t' '{print $1"\t"$4}' "$BASE/inventory.names" | sort -u) \
    <(awk -F'\t' '{print $1"\t"$4}' "$cur" | sort -u) \
  | awk -F'\t' '$2 != $3 {print $1}')
[[ -z "$drift" ]] && ok "all surviving statements byte-identical (normalized)" \
                  || bad "STATEMENT DRIFT in: $drift"

echo "== H6 privacy =="
pdrift=$(join -t$'\t' -j1 \
    <(awk -F'\t' '{print $1"\t"$3}' "$BASE/inventory.names" | sort -u) \
    <(awk -F'\t' '{print $1"\t"$3}' "$cur" | sort -u) \
  | awk -F'\t' '$2 != $3 {print $1}')
pbad=$(comm -23 <(printf '%s\n' $pdrift | sort -u) <(printf '%s\n' $ALLOW_PRO)) || true
[[ -z "$pbad" ]] && ok "privacy changes all whitelisted" || bad "UNWHITELISTED privacy change: $pbad"

echo "== H5 diff shape =="
baserev=$(grep '^rev: ' "$BASE/META.txt" | awk '{print $2}')
offplan=$(git diff --name-only "$baserev" -- . | grep -vxF -f <(printf '%s\n' "${ALLOW_FILES[@]}") ) || true
[[ -z "$offplan" ]] && ok "only planned files touched" || bad "OFF-PLAN files changed: $offplan"

if [[ "${1:-}" == "--axioms" ]]; then
  echo "== H3 axiom surface (kernel) =="
  probe=$(mktemp); echo "import QuantumInfo" > "$probe"
  awk -F'\t' '($2=="theorem"||$2=="lemma") && $3=="public" {print "#print axioms " $1}' "$cur.tsv" \
    | sort -u >> "$probe"
  lake env lean "$probe" 2>&1 | grep "depends on axioms" | sort > "$cur.ax"
  if diff -q "$BASE/axioms.txt" "$cur.ax" >/dev/null 2>&1; then ok "axiom surface identical"
  else bad "AXIOM SURFACE CHANGED:"; diff "$BASE/axioms.txt" "$cur.ax" | head -20; fi
  rm -f "$probe" "$cur.ax"
fi
rm -f "$cur" "$cur.tsv"
echo; [[ $fail -eq 0 ]] && echo "ALL CHECKS PASSED" || { echo "CHECKS FAILED — do not proceed"; exit 1; }
