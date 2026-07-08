#!/usr/bin/env bash
# lib.sh — shared extractor for the PR2 move-refactor harness.
#
# extract_inventory <file.lean>
#   Emits one TSV row per declaration:  name<TAB>kind<TAB>privacy<TAB>stmt_sha16<TAB>file<TAB>line
#   - "statement block" = attribute lines (@[...]) + the declaration head through the first
#     line containing ':=' (text after ':=' dropped: proofs are NOT fidelity-checked).
#     Docstrings are EXCLUDED (comments may legitimately be reworded in a move).
#   - lines are whitespace-normalized and joined with the literal 2-char sequence '\n',
#     so each declaration is exactly ONE output record; the join marker is deterministic
#     on both sides of the refactor, which is all fidelity needs.
#
# KNOWN LIMITATIONS (compensating control: human review of 00_manifest output in P1):
#   * anonymous `instance :` declarations are keyed instance@<line>
#   * `notation` rows are keyed by their first quoted token
#   * decl heads not matching the keyword pattern below are not inventoried
#   * a ':=' inside a comment/string on the head lines would mis-slice; none in the
#     current move-set (spot-checked at 720c9fff)

set -u

extract_inventory() {
  local f="$1"
  awk -v FNAME="$f" '
    function norm(s) { gsub(/[ \t]+/, " ", s); sub(/[ \t]+$/, "", s); sub(/^ /, "", s); return s }
    BEGIN { attrs = ""; inblock = 0 }
    /^@\[/ && !inblock { attrs = attrs norm($0) "\\n"; next }
    !inblock && /^(private[ \t]+)?(noncomputable[ \t]+)?(theorem|lemma|def|abbrev|instance|structure|axiom|notation)[ \t]/ {
      inblock = 1
      block = attrs
      priv = ($0 ~ /^private/) ? "private" : "public"
      line0 = FNR
      hd = $0
      sub(/^private[ \t]+/, "", hd); sub(/^noncomputable[ \t]+/, "", hd)
      kind = hd; sub(/[ \t].*/, "", kind)
      rest = hd; sub(/^[a-z]+[ \t]+/, "", rest)
      if (kind == "notation") {
        name = rest; sub(/^[^"]*"/, "", name); sub(/".*/, "", name); name = "notation:" name
      } else {
        name = rest; sub(/[ \t({:\[].*/, "", name)
        if (name == "") name = kind "@" FNR
      }
    }
    inblock {
      l = $0
      if (index(l, ":=") > 0) {
        sub(/:=.*/, ":=", l)
        block = block norm(l)
        printf "%s\t%s\t%s\t%s\t%s\t%d\n", name, kind, priv, block, FNAME, line0
        inblock = 0; attrs = ""
      } else {
        block = block norm(l) "\\n"
      }
      next
    }
    { attrs = "" }
  ' "$f" | while IFS=$'\t' read -r name kind priv blob file line; do
      sha=$(printf '%s' "$blob" | shasum -a 256 | cut -c1-16)
      printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$name" "$kind" "$priv" "$sha" "$file" "$line"
    done
}
