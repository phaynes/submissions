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
# File-agnostic MULTISET record per declaration (Codex "multiset not name-set"): the move
# changes a decl's file, so file is NOT part of the identity — but names collide (two
# `conj_supportProj_eq_of_ker_le` privates; `def mix` vs `abbrev mix`; two `[…]` notations),
# so identity = name+kind+privacy+statement-hash, and we compare the SORTED MULTISET of
# these records. A pure move leaves the multiset unchanged.
recset() { awk -F'\t' '{print $1"\t"$2"\t"$3"\t"$4}' "$1" | sort; }
recset "$BASE/inventory.tsv" > "$cur.base"
recset "$cur.tsv"            > "$cur.cur"

echo "== H1/H2/H6 inventory + fidelity + privacy (multiset of name/kind/privacy/stmt-hash) =="
# Records present in baseline but not now (removed OR statement/privacy changed):
gone=$(comm -23 "$cur.base" "$cur.cur")
# Records present now but not in baseline (added OR statement/privacy changed):
new=$(comm -13 "$cur.base" "$cur.cur")
# A record that only moved file is identical here, so vanishes from both -> the diff shows
# ONLY genuine changes. Classify by name against the whitelist.
gone_names=$(printf '%s\n' "$gone" | awk -F'\t' 'NF{print $1}' | sort -u)
new_names=$(printf '%s\n' "$new"  | awk -F'\t' 'NF{print $1}' | sort -u)
allow_new=$(printf '%s\n%s\n' "$ALLOW_ADD" "$ALLOW_PRO" | grep -v '^$' | sort -u)
allow_gone=$(printf '%s\n%s\n' "$ALLOW_DEL" "$ALLOW_PRO" | grep -v '^$' | sort -u)
bad_new=$(comm -23 <(printf '%s\n' $new_names | sort -u)  <(printf '%s\n' $allow_new)) || true
bad_gone=$(comm -23 <(printf '%s\n' $gone_names | sort -u) <(printf '%s\n' $allow_gone)) || true
if [[ -z "$bad_gone" ]]; then ok "no unwhitelisted removals / statement-drift / privacy-drop"
else bad "UNWHITELISTED change (lost decl OR statement/privacy drift): $bad_gone"
     printf '%s\n' "$gone" | grep -Ff <(printf '%s\n' $bad_gone) | sed 's/^/     was: /' | head; fi
if [[ -z "$bad_new" ]]; then ok "no unwhitelisted additions"
else bad "UNWHITELISTED addition: $bad_new"
     printf '%s\n' "$new" | grep -Ff <(printf '%s\n' $bad_new) | sed 's/^/     now: /' | head; fi

echo "== H5 diff shape =="
baserev=$(grep '^rev: ' "$BASE/META.txt" | awk '{print $2}')
offplan=$(git diff --name-only "$baserev" -- . | grep -vxF -f <(printf '%s\n' "${ALLOW_FILES[@]}") ) || true
[[ -z "$offplan" ]] && ok "only planned files touched" || bad "OFF-PLAN files changed: $offplan"

if [[ "${1:-}" == "--axioms" ]]; then
  echo "== H3 axiom surface (kernel) =="
  # Names introduced/promoted by the refactor are legitimately absent from the baseline
  # (Codex B2). Exclude them from the strict diff, then assert THEY are sorryAx-free.
  NEWNAMES=$(printf '%s\n%s\n' "$ALLOW_ADD" "$ALLOW_PRO" | grep -v '^$' | sort -u)
  probe=$(mktemp); echo "import QuantumInfo" > "$probe"
  awk -F'\t' '($2=="theorem"||$2=="lemma") && $3=="public" {print "#print axioms " $1}' \
    "$cur.tsv" | sort -u >> "$probe"
  # `lake env lean` on a #print-only file may exit non-zero / write to stderr even on
  # success; run WITHOUT pipefail so its exit code does not abort the check.
  set +o pipefail
  lake env lean "$probe" 2>&1 | grep "depends on axioms" | sort > "$cur.ax" || true
  set -o pipefail
  # strict comparison EXCLUDING the whitelisted new/promoted names on both sides
  excl=$(printf "%s\n" "$NEWNAMES" | sed "s/.*/^'&'/" | paste -sd'|' -)
  if [[ -n "$excl" ]]; then
    grep -Ev "$excl" "$BASE/axioms.txt" > "$cur.axb" || true
    grep -Ev "$excl" "$cur.ax"        > "$cur.axc" || true
  else cp "$BASE/axioms.txt" "$cur.axb"; cp "$cur.ax" "$cur.axc"; fi
  if diff -q "$cur.axb" "$cur.axc" >/dev/null 2>&1; then ok "axiom surface identical (excl. whitelisted)"
  else bad "AXIOM SURFACE CHANGED:"; diff "$cur.axb" "$cur.axc" | head -20; fi
  # For any whitelisted new/promoted name that IS present (i.e. post-refactor), assert it
  # is sorryAx-free. A name that is absent is fine PRE-refactor (nothing moved yet); H1's
  # `new`-record classification separately enforces that post-refactor additions are
  # whitelisted. NB: set -e safe — a `grep -q` miss returns 1 and must not abort.
  if [[ -n "$NEWNAMES" ]]; then
    wl_ok=1; wl_seen=0
    while read -r n; do
      [[ -z "$n" ]] && continue
      row=$(grep -F "'$n' depends on axioms" "$cur.ax" || true)
      [[ -z "$row" ]] && continue
      wl_seen=1
      if printf '%s' "$row" | grep -q sorryAx; then bad "H3: whitelisted '$n' has sorryAx"; wl_ok=0; fi
    done <<< "$NEWNAMES"
    if [[ $wl_seen -eq 0 ]]; then echo "  (whitelisted additions not present yet — pre-refactor no-op)"
    elif [[ $wl_ok -eq 1 ]]; then ok "whitelisted additions present & sorryAx-free"; fi
  fi
  rm -f "$probe" "$cur.ax" "$cur.axb" "$cur.axc"

  echo "== H4 kernel signature fidelity (elaborated types; Codex B4) =="
  # Guards elaborated-type drift on a move (source-identical, type-different). Each line of
  # sig.hashes is "sha16<TAB>name"; compare per-name over the intersection (new/promoted
  # names have no baseline sig and are covered by H3's sorryAx assertion).
  if [[ -f "$BASE/sig.hashes" ]]; then
    cp "$HERE/sig_check.lean" "$PHYSLIB/sig_check.lean"
    awk -F'\t' '$3=="public"{print $1}' "$cur.tsv" | sort -u > "$PHYSLIB/sig_names.txt"
    set +o pipefail
    ( cd "$PHYSLIB" && lake env lean --run sig_check.lean 2>/dev/null ) \
      | sed -E 's/_@\.[A-Za-z0-9_.]*_hyg[A-Za-z0-9._]*/_HYG_/g' \
      | while IFS= read -r rec; do
          n=$(printf '%s' "$rec" | cut -d' ' -f1)
          h=$(printf '%s' "$rec" | shasum -a 256 | cut -c1-16)
          printf '%s\t%s\n' "$h" "$n"
        done | sort -k2 > "$cur.sig" || true
    set -o pipefail
    rm -f "$PHYSLIB/sig_check.lean" "$PHYSLIB/sig_names.txt"
    # a MISSING marker means a public decl vanished from the kernel — loud failure
    if awk -F'\t' '$2=="MISSING"' "$cur.sig" | grep -q .; then
      bad "H4: public declaration(s) MISSING from kernel:"; awk -F'\t' '$2=="MISSING"{print "     "$1}' "$cur.sig" | head
    fi
    # per-name hash comparison over the intersection of baseline & current names
    sdrift=$(join -1 2 -2 2 <(sort -k2 "$BASE/sig.hashes") <(sort -k2 "$cur.sig") \
      | awk '$2 != $3 {print $1}')
    if [[ -z "$sdrift" ]]; then ok "elaborated signatures identical for all surviving public decls"
    else bad "ELABORATED TYPE DRIFT (source may be identical; kernel type changed): $sdrift"; fi
    rm -f "$cur.sig"
  else
    echo "  (skip — no baseline sig.hashes; run 10_baseline.sh --axioms first)"
  fi
fi
rm -f "$cur" "$cur.tsv" "$cur.base" "$cur.cur"
echo; [[ $fail -eq 0 ]] && echo "ALL CHECKS PASSED" || { echo "CHECKS FAILED — do not proceed"; exit 1; }
