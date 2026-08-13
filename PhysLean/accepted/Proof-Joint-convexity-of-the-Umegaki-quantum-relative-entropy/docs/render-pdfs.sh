#!/usr/bin/env bash
# render-pdfs.sh — render the docs/*.qmd notes to PDF, correctly, and verify it.
#
# The docs render as HTML by default (format: html in each file). This script renders
# the PDF companions using the shared _pdf-format.yml, then checks the two failure
# modes that have bitten these documents before and fails loudly if either recurs:
#
#   1. Double section numbers ("1 1.", "2 2." ...) — happens when number-sections is
#      left true while the headings already carry manual numbers. _pdf-format.yml sets
#      number-sections: false; this script confirms no "N N." heading survived.
#   2. Silently dropped glyphs — xelatex omits a character with no glyph in the active
#      font (Greek, subscripts, relation symbols in prose/code). _pdf-format.yml maps
#      each such symbol via \newunicodechar; this script re-runs xelatex on the
#      generated .tex and fails if the log reports ANY "Missing character".
#
# Usage:  ./render-pdfs.sh          (run from the docs/ directory; needs quarto + xelatex)
# Exit:   0 iff every doc rendered and both checks passed for all of them.

set -u
here="$(cd "$(dirname "$0")" && pwd)"
cd "$here"

cfg="_pdf-format.yml"
docs=(literature physics-brief proof-conventional)

command -v quarto  >/dev/null || { echo "FATAL: quarto not found";  exit 3; }
command -v xelatex >/dev/null || { echo "FATAL: xelatex not found"; exit 3; }

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

green() { printf '\033[32m%s\033[0m\n' "$1"; }
red()   { printf '\033[31m%s\033[0m\n' "$1"; }

fail=0
for f in "${docs[@]}"; do
  echo "── $f ──────────────────────────────────────────"

  # Render PDF (and keep the .tex so we can audit glyphs independently of quarto).
  if ! quarto render "$f.qmd" --to pdf --metadata-file "$cfg" --metadata keep-tex:true \
        >"$work/$f.render.log" 2>&1; then
    red "  render FAILED (see $work/$f.render.log)"; fail=1; continue
  fi
  [ -f "$f.pdf" ] || { red "  no $f.pdf produced"; fail=1; continue; }
  green "  rendered $f.pdf"

  # Check 1: no double-numbered headings in the PDF text.
  dbl="$(python3 - "$f.pdf" <<'PY'
import sys, re
from pypdf import PdfReader
txt="\n".join((p.extract_text() or "") for p in PdfReader(sys.argv[1]).pages)
bad=[ln.strip() for ln in txt.splitlines() if re.match(r'^\s*(\d+)\s+\1\.\s', ln)]
print("\n".join(bad))
PY
)"
  if [ -n "$dbl" ]; then
    red "  DOUBLE-NUMBERED HEADINGS found:"; printf '    %s\n' "$dbl"; fail=1
  else
    green "  section numbers clean (no \"N N.\")"
  fi

  # Check 2: xelatex reports no missing characters for the generated .tex.
  if [ -f "$f.tex" ]; then
    cp "$f.tex" "$work/"
    ( cd "$work" && xelatex -interaction=nonstopmode "$f.tex" >/dev/null 2>&1 )
    miss="$(grep -c "Missing character" "$work/$f.log" 2>/dev/null)"
    miss="${miss:-0}"
    if [ "$miss" -gt 0 ]; then
      red "  $miss MISSING-CHARACTER warning(s) — a glyph is being dropped:"
      grep "Missing character" "$work/$f.log" | sed -E 's/.*There is no (.*) in font.*/    \1/' | sort | uniq -c
      fail=1
    else
      green "  no missing glyphs"
    fi
    rm -f "$f.tex"
  else
    red "  expected $f.tex (keep-tex) but it was not produced"; fail=1
  fi
done

echo "───────────────────────────────────────────────────"
if [ "$fail" -eq 0 ]; then
  green "ALL DOCS OK — PDFs rendered, numbering clean, no dropped glyphs."
else
  red "FAILURES above — see messages."
fi
exit "$fail"
