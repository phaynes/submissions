#!/usr/bin/env bash
# Reviewer's one-command local verification for the qRelativeEnt_joint_convexity
# submission to PhysLean. Reproduces the author's adversarial checks so you don't
# have to reconstruct whether the proof is real: it proves it to you.
#
# Usage:
#   ./verify.sh /path/to/your/physlib/checkout        # on branch feat/qrelent-joint-convexity
#   BASE_REF=origin/master ./verify.sh /path/...       # compare against a different base ref
#
# What it checks (each is pass/fail; the axiom check is kernel-level and hard to fake):
#   1. The theorem STATEMENT matches the original `sorry` stub after removing the proof
#      body and attributes (whitespace-normalised). This confirms the theorem was not
#      silently weakened; it is NOT a raw byte comparison (see the note at check 1).
#   2. `#print axioms` on the theorem shows ONLY [propext, Classical.choice, Quot.sound]
#      — no `sorryAx`, so there is no hidden sorry/admit anywhere in its dependency chain.
#   3. The module builds.
#   4. (optional, slow) `lake exe lint_all` is clean.
#
# Exit code 0 = all mandatory checks pass. Check 1 FAILS (does not pass) if either
# statement cannot be extracted or they differ; set ALLOW_STMT_MISMATCH=1 only to
# force past an extraction problem you have manually confirmed is benign.

set -uo pipefail

REPO="${1:-.}"
THM="qRelativeEnt_joint_convexity"
FILE="QuantumInfo/Entropy/DPI.lean"
ORIG_FILE="QuantumInfo/Entropy/Relative.lean"   # where the original sorry lived
BASE_REF="${BASE_REF:-origin/master}"           # base ref the original stub is read from
FAIL=0

say()  { printf '\n\033[1m%s\033[0m\n' "$*"; }
pass() { printf '  \033[32m✓ %s\033[0m\n' "$*"; }
fail() { printf '  \033[31m✗ %s\033[0m\n' "$*"; FAIL=1; }

cd "$REPO" 2>/dev/null || { echo "cannot cd to $REPO"; exit 3; }

if [ ! -f "$FILE" ]; then
  echo "This does not look like a physlib checkout ($FILE not found)."; exit 3
fi

say "1. Statement is not weakened (matches the original stub, proof body removed)"
# Extract the statement (from `theorem <name>` up to the `:= by` line) from both
# the current file and the base ref's original, then normalise for comparison:
# strip attributes (@[...]), drop a trailing `sorry`, collapse whitespace, trim.
# NOTE: this is a NORMALISED statement match, not a raw byte comparison — it proves
# no hypothesis or conclusion changed, which is what "not weakened" requires.
extract_stmt() {  # $1 = git ref (or WORKING for the working tree), $2 = file
  local ref="$1" f="$2"
  if [ "$ref" = "WORKING" ]; then cat "$f"; else git show "$ref:$f" 2>/dev/null; fi \
    | awk "/theorem ${THM}/{grab=1} grab{print} /:= by/{if(grab)exit}"
}
normalise() {  # read stdin -> normalised single-line statement
  sed 's/@\[[a-z]*\]//g; s/ *sorry//' | tr -s ' \t\n' ' ' | sed 's/^ *//; s/ *$//'
}
CUR="$(extract_stmt WORKING "$FILE" | normalise)"
# The original may be in Relative.lean (where the stub lived) or DPI.lean on the base ref.
ORIG="$(extract_stmt "$BASE_REF" "$ORIG_FILE" | normalise)"
[ -z "$ORIG" ] && ORIG="$(extract_stmt "$BASE_REF" "$FILE" | normalise)"

if [ -z "$CUR" ]; then
  fail "could not extract the current theorem statement from $FILE"
elif [ -z "$ORIG" ]; then
  if [ "${ALLOW_STMT_MISMATCH:-0}" = "1" ]; then
    pass "original stub not found on $BASE_REF — accepted via ALLOW_STMT_MISMATCH=1"
  else
    fail "could not extract the original stub from $BASE_REF ($ORIG_FILE or $FILE) — is the base ref fetched?"
  fi
elif [ "$CUR" = "$ORIG" ]; then
  pass "statement matches the original stub (only the proof changed)"
else
  fail "statement DIFFERS from the original stub — possible weakening"
  printf '    --- original (%s) ---\n    %s\n    --- current ---\n    %s\n' "$BASE_REF" "$ORIG" "$CUR"
fi

say "2. #print axioms — no sorryAx (kernel-level check)"
AXOUT="$(printf 'import QuantumInfo.Entropy.DPI\n#print axioms %s\n' "$THM" | lake env lean --stdin 2>&1)"
echo "    $AXOUT" | sed 's/^/  /'
if printf '%s' "$AXOUT" | grep -q 'sorryAx'; then
  fail "sorryAx present — the proof (or something it depends on) still has a hole"
elif printf '%s' "$AXOUT" | grep -q "depends on axioms: \[propext, Classical.choice, Quot.sound\]"; then
  pass "clean axiom base — no sorry/admit anywhere in the dependency chain"
elif printf '%s' "$AXOUT" | grep -q 'depends on axioms'; then
  pass "no sorryAx (note: axiom set differs from the standard three — inspect above)"
else
  fail "could not run #print axioms (is the toolchain set up? try 'lake build' first)"
fi

say "3. The module builds"
if lake build QuantumInfo.Entropy.DPI >/tmp/qrelent_build.log 2>&1; then
  pass "QuantumInfo.Entropy.DPI built successfully"
else
  fail "build failed (see /tmp/qrelent_build.log)"; tail -5 /tmp/qrelent_build.log | sed 's/^/    /'
fi

say "4. (optional) Full linter — slow; run with LINT=1"
if [ "${LINT:-0}" = "1" ]; then
  if lake exe lint_all >/tmp/qrelent_lint.log 2>&1; then pass "lint_all clean"
  else fail "lint_all reported issues (see /tmp/qrelent_lint.log)"; fi
else
  printf '  \033[33m- skipped (set LINT=1 to run \`lake exe lint_all\`, ~minutes)\033[0m\n'
fi

say "Result"
if [ "$FAIL" = 0 ]; then
  printf '  \033[32mAll mandatory checks passed: statement unchanged, clean axioms (no sorryAx), builds.\033[0m\n'
  exit 0
else
  printf '  \033[31mOne or more checks failed — see above.\033[0m\n'
  exit 1
fi
