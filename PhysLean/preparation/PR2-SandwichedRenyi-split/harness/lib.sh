#!/usr/bin/env bash
# lib.sh — shared extractor for the PR2 move-refactor harness.
#
# extract_inventory <file.lean>
#   Emits one TSV row per declaration:  name<TAB>kind<TAB>privacy<TAB>stmt_sha16<TAB>file<TAB>line
#
#   - `notation` (and other head-only commands) are emitted as ONE record on their own head
#     line — they have no ':=' and MUST NOT put the parser into ':='-waiting mode, or they
#     swallow the following declaration (Codex review B1). Verified by the self-test in
#     10_baseline.sh.
#   - For value declarations (theorem/lemma/def/...), the "statement block" = attribute
#     lines (@[...]) + the head through the first line containing ':=' (text after ':='
#     dropped: proofs are NOT fidelity-checked here — that is what H2 covers; H4/sig_check
#     cover elaborated types). Docstrings are excluded (comments may be reworded in a move).
#   - Whitespace-normalized; each declaration is exactly ONE output record.
#
# KNOWN LIMITATIONS (compensating control: human review of 00_manifest output in P1):
#   * anonymous `instance :` declarations are keyed instance@<line>
#   * a ':=' inside a comment/string on the head lines would mis-slice (none in the move-set)

set -u

extract_inventory() {
  local f="$1"
  awk -v FNAME="$f" '
    function norm(s) { gsub(/[ \t]+/, " ", s); sub(/[ \t]+$/, "", s); sub(/^ /, "", s); return s }
    function emit(nm, kind, priv, block, line) {
      printf "%s\t%s\t%s\t%s\t%s\t%d\n", nm, kind, priv, block, FNAME, line
    }
    BEGIN { attrs = ""; inblock = 0 }
    /^@\[/ && !inblock { attrs = attrs norm($0) "\\n"; next }

    # head-only commands: notation / infix* / prefix / postfix / macro_rules etc. — single record, no := wait
    !inblock && /^(scoped[ \t]+)?(notation|infixl|infixr|infix|prefix|postfix)[ \t]/ {
      priv = "public"
      hd = $0; sub(/^scoped[ \t]+/, "", hd)
      kind = hd; sub(/[ \t].*/, "", kind)
      name = hd; sub(/^[a-z_]+[ \t]+/, "", name)
      if (name ~ /"/) { sub(/^[^"]*"/, "", name); sub(/".*/, "", name) } else { sub(/[ \t].*/, "", name) }
      name = "notation:" name
      emit(name, kind, priv, norm($0), FNR)
      attrs = ""
      next
    }

    !inblock && /^(private[ \t]+)?(noncomputable[ \t]+)?(theorem|lemma|def|abbrev|instance|structure|axiom)[ \t]/ {
      inblock = 1
      block = attrs
      priv = ($0 ~ /^private/) ? "private" : "public"
      line0 = FNR
      hd = $0
      sub(/^private[ \t]+/, "", hd); sub(/^noncomputable[ \t]+/, "", hd)
      kind = hd; sub(/[ \t].*/, "", kind)
      rest = hd; sub(/^[a-z]+[ \t]+/, "", rest)
      name = rest; sub(/[ \t({:\[].*/, "", name)
      if (name == "") name = kind "@" FNR
    }
    inblock {
      l = $0
      if (index(l, ":=") > 0) {
        sub(/:=.*/, ":=", l)
        block = block norm(l)
        emit(name, kind, priv, block, line0)
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
