#!/usr/bin/env bash
#
# submit.sh — step through opening the PhysLean PR for qRelativeEnt_joint_convexity.
#
# This is a GUIDED, INTERACTIVE script. It does nothing outward-facing without asking
# you first (every push / fork / PR-create step prompts y/N). Read-only checks run
# without prompting. You can quit at any prompt with 'q' or Ctrl-C and rerun later;
# each step is idempotent where it can be.
#
# What it walks you through:
#   0. sanity: right branch, right commit, clean tree, gh authed
#   1. run the packet verifier (statement / #print axioms / build), then LINT=1
#   2. run the upstream style linters directly (lint_all, lint-style.sh)
#   3. choose how to publish the branch: your fork (default) or a direct push
#   4. push the branch
#   5. open the PR non-draft with the packet's title + PR-BODY.md, tag t-quantumInfo
#   6. print the follow-up checklist (Zulip announce, respond to review)
#
# Usage:
#   ./submit.sh /path/to/physlib-checkout
#     (defaults to the checkout this packet was verified against if omitted)

set -uo pipefail

# ---- config ---------------------------------------------------------------------
PKG_DIR="$(cd "$(dirname "$0")" && pwd)"
PHYSLIB_DEFAULT="/Volumes/second-store/devel/knowledge-base-mcp/mentormind/physlib-contrib"
PHYSLIB="${1:-$PHYSLIB_DEFAULT}"

BRANCH="feat/qrelent-joint-convexity"
EXPECTED_COMMIT="a1303c7bd27ba2078c4acac618c1764b9efce745"   # the AI-trailer commit (Codex-refined refactor)
UPSTREAM_SLUG="leanprover-community/physlib"
BASE_BRANCH="master"
PR_TITLE="feat(QuantumInfo): prove qRelativeEnt_joint_convexity"
PR_TAG="t-quantumInfo"

# ---- ui helpers -----------------------------------------------------------------
bold() { printf '\033[1m%s\033[0m\n' "$*"; }
ok()   { printf '  \033[32m✓ %s\033[0m\n' "$*"; }
warn() { printf '  \033[33m! %s\033[0m\n' "$*"; }
err()  { printf '  \033[31m✗ %s\033[0m\n' "$*"; }
step() { printf '\n\033[1;36m━━ %s\033[0m\n' "$*"; }

# This script must be run interactively (it prompts before every outward-facing step).
if [ ! -t 0 ] && [ ! -r /dev/tty ]; then
  echo "submit.sh must be run in an interactive terminal (it asks before each push/PR step)." >&2
  echo "Run it directly:  ./submit.sh /path/to/physlib-checkout" >&2
  exit 2
fi

# ask "question" -> returns 0 for yes, 1 for no, exits on q. Reads from the terminal.
ask() {
  local reply=""
  while true; do
    printf '  \033[35m? %s\033[0m [y/N/q] ' "$1"
    if [ -r /dev/tty ]; then read -r reply </dev/tty; else read -r reply; fi
    case "$reply" in
      y|Y) return 0 ;;
      n|N|'') return 1 ;;
      q|Q) echo "  aborted — nothing further done."; exit 0 ;;
      *) echo "    please answer y, n, or q" ;;
    esac
  done
}

gitc() { git -C "$PHYSLIB" "$@"; }

# ---- 0. sanity ------------------------------------------------------------------
step "Step 0 — sanity checks (read-only)"

[ -d "$PHYSLIB/.git" ] || { err "not a git checkout: $PHYSLIB"; exit 2; }
ok "physlib checkout: $PHYSLIB"

if ! command -v gh >/dev/null; then err "'gh' CLI not found — install it or open the PR in the browser"; exit 2; fi
if ! gh auth status >/dev/null 2>&1; then err "gh not authenticated — run 'gh auth login'"; exit 2; fi
ok "gh authenticated as: $(gh api user -q .login 2>/dev/null || echo '?')"

CUR_BRANCH="$(gitc rev-parse --abbrev-ref HEAD)"
if [ "$CUR_BRANCH" != "$BRANCH" ]; then
  warn "checkout is on '$CUR_BRANCH', not the PR branch '$BRANCH'."
  if ask "switch to $BRANCH now?"; then
    gitc checkout "$BRANCH" || { err "checkout failed (commit/stash your work first)"; exit 2; }
  else
    err "the PR must be pushed from '$BRANCH'. Aborting."; exit 2
  fi
fi
ok "on branch $BRANCH"

HEAD_COMMIT="$(gitc rev-parse HEAD)"
if [ "$HEAD_COMMIT" != "$EXPECTED_COMMIT" ]; then
  warn "HEAD is $HEAD_COMMIT"
  warn "expected  $EXPECTED_COMMIT (the reviewed commit with AI trailers)"
  warn "if you re-amended intentionally, that's fine; otherwise stop and check."
  ask "continue with the current HEAD anyway?" || { echo "  stopped."; exit 0; }
else
  ok "HEAD is the expected reviewed commit ($HEAD_COMMIT)"
fi

# working tree must be clean (untracked files are allowed)
if [ -n "$(gitc status --porcelain --untracked-files=no)" ]; then
  err "working tree has uncommitted changes — commit or stash before submitting:"
  gitc status --short | sed 's/^/      /'
  exit 2
fi
ok "working tree clean (tracked files)"

bold "Diff that will be proposed (vs $BASE_BRANCH):"
gitc --no-pager diff --stat "$BASE_BRANCH...$BRANCH" | sed 's/^/    /'

# ---- 1. packet verifier ---------------------------------------------------------
step "Step 1 — packet verifier (statement / #print axioms / build)"
if ask "run ./verify.sh against this checkout?"; then
  BASE_REF="$BASE_BRANCH" bash "$PKG_DIR/verify.sh" "$PHYSLIB" || {
    err "verify.sh reported a failure — resolve before submitting."; exit 2; }
  ok "verify.sh passed"
  if ask "also run the slow lint pass (LINT=1: lint_all + lint-style.sh)?"; then
    LINT=1 BASE_REF="$BASE_BRANCH" bash "$PKG_DIR/verify.sh" "$PHYSLIB" || {
      err "lint pass failed — resolve before submitting."; exit 2; }
    ok "LINT=1 pass clean"
  fi
else
  warn "skipped verifier — only do this if you have already run it."
fi

# ---- 2. (handled inside step 1 if chosen) --------------------------------------

# ---- 3. choose publish target ---------------------------------------------------
step "Step 3 — how to publish branch '$BRANCH'"
echo "  Upstream is $UPSTREAM_SLUG. You likely cannot push to it directly;"
echo "  the normal flow is fork -> push to your fork -> PR from the fork."
echo
echo "    [f] fork  : push to YOUR fork of physlib, open PR from there   (recommended)"
echo "    [d] direct: push $BRANCH straight to $UPSTREAM_SLUG            (needs write access)"
echo "    [q] quit"
PUSH_MODE=""
while [ -z "$PUSH_MODE" ]; do
  printf '  \033[35m? choose f / d / q: \033[0m'; read -r m </dev/tty
  case "$m" in
    f|F) PUSH_MODE=fork ;;
    d|D) PUSH_MODE=direct ;;
    q|Q) echo "  stopped."; exit 0 ;;
    *) echo "    f, d, or q" ;;
  esac
done

# ---- 4. push --------------------------------------------------------------------
step "Step 4 — push the branch"
HEAD_REPO_FLAG=""     # for gh pr create
if [ "$PUSH_MODE" = "fork" ]; then
  GH_USER="$(gh api user -q .login)"
  FORK_SLUG="$GH_USER/physlib"
  echo "  Ensuring your fork $FORK_SLUG exists..."
  if gh repo view "$FORK_SLUG" >/dev/null 2>&1; then
    ok "fork exists: $FORK_SLUG"
  else
    if ask "fork $UPSTREAM_SLUG to $FORK_SLUG now?"; then
      gh repo fork "$UPSTREAM_SLUG" --clone=false || { err "fork failed"; exit 2; }
      ok "forked"
    else
      err "need a fork to push to. Aborting."; exit 2
    fi
  fi
  # add a 'fork' remote if missing
  if ! gitc remote get-url fork >/dev/null 2>&1; then
    gitc remote add fork "https://github.com/$FORK_SLUG.git"
    ok "added remote 'fork' -> $FORK_SLUG"
  fi
  echo
  bold "About to run:  git push -u fork $BRANCH   (publishes to YOUR fork)"
  if ask "push $BRANCH to your fork now?"; then
    gitc push -u fork "$BRANCH" || { err "push failed"; exit 2; }
    ok "pushed to fork"
  else
    echo "  stopped before pushing."; exit 0
  fi
  HEAD_REPO_FLAG="--head $GH_USER:$BRANCH"
else
  echo
  bold "About to run:  git push -u origin $BRANCH   (publishes to UPSTREAM $UPSTREAM_SLUG)"
  warn "this pushes directly to the upstream project. Only do this with write access."
  if ask "push $BRANCH to $UPSTREAM_SLUG now?"; then
    gitc push -u origin "$BRANCH" || { err "push failed (no write access? use the fork flow)"; exit 2; }
    ok "pushed to upstream"
  else
    echo "  stopped before pushing."; exit 0
  fi
  HEAD_REPO_FLAG="--head $BRANCH"
fi

# ---- 5. open the PR -------------------------------------------------------------
step "Step 5 — open the pull request (non-draft)"
echo "  Title: $PR_TITLE"
echo "  Base:  $UPSTREAM_SLUG : $BASE_BRANCH"
echo "  Body:  PR-BODY.md (the fenced Body block is the PR description)"
echo "  Label: $PR_TAG"
echo
warn "PR-BODY.md wraps the description in a \`\`\`markdown fence with two OPTIONAL"
warn "comment blocks after it. Post ONLY the Body block as the PR description, then add"
warn "the optional comments as separate PR comments if you want them."
echo
if ask "open the PR now with 'gh pr create'?"; then
  # Extract just the fenced Body block from PR-BODY.md into a temp file.
  # The Body is a ```markdown ... ``` fence that itself CONTAINS nested ``` fences
  # (the bash/text check blocks), so we can't count fences. Instead we take everything
  # from the line after the Body's opening ```markdown up to the line before the
  # "## Optional ..." header, then drop the single trailing ``` fence.
  BODY_TMP="$(mktemp)"
  awk '
    /^## Optional supporting-material comment/ {stop=1}
    stop {next}
    capture {print}
    /^\*\*Body\*\*/ {seen_body=1}
    seen_body && !capture && /^```markdown$/ {capture=1; seen_body=0}
  ' "$PKG_DIR/PR-BODY.md" \
    | awk '
        {lines[NR]=$0}
        END{
          last=NR
          # strip trailing blank lines, "---" separators, and the closing ``` fence
          while(last>0 && (lines[last] ~ /^[[:space:]]*$/ || lines[last]=="---" || lines[last]=="```")) last--
          for(i=1;i<=last;i++) print lines[i]
        }' \
    > "$BODY_TMP"

  if [ ! -s "$BODY_TMP" ]; then
    warn "couldn't auto-extract the Body block; opening \$EDITOR via gh instead."
    gh pr create --repo "$UPSTREAM_SLUG" --base "$BASE_BRANCH" $HEAD_REPO_FLAG \
      --title "$PR_TITLE" --label "$PR_TAG" || {
        warn "label may not exist / no perms; retrying without --label"
        gh pr create --repo "$UPSTREAM_SLUG" --base "$BASE_BRANCH" $HEAD_REPO_FLAG --title "$PR_TITLE"; }
  else
    bold "PR body preview (first 20 lines):"
    sed -n '1,20p' "$BODY_TMP" | sed 's/^/    /'
    echo "    ..."
    if ask "looks right — create the PR?"; then
      if ! gh pr create --repo "$UPSTREAM_SLUG" --base "$BASE_BRANCH" $HEAD_REPO_FLAG \
             --title "$PR_TITLE" --body-file "$BODY_TMP" --label "$PR_TAG"; then
        warn "create failed (label missing or no perms?); retrying without --label"
        gh pr create --repo "$UPSTREAM_SLUG" --base "$BASE_BRANCH" $HEAD_REPO_FLAG \
          --title "$PR_TITLE" --body-file "$BODY_TMP"
      fi
      ok "PR created"
    else
      echo "  did not create the PR. Body draft left at: $BODY_TMP"
      exit 0
    fi
  fi
  rm -f "$BODY_TMP"
else
  echo "  stopped before creating the PR."; exit 0
fi

# ---- 6. follow-ups --------------------------------------------------------------
step "Step 6 — after the PR is open (manual follow-ups)"
cat <<'NEXT'
  1. Verify AI disclosure: the commit carries the Co-authored-by trailers and the PR
     body has the "AI assistance" section (both already in place).
  2. Post the OPTIONAL supporting-material comment (from PR-BODY.md) as a PR comment,
     if you want reviewers to have the docs/paper/evidence links.
  3. Announce on the PhysLean Zulip if that is the project's convention.
  4. Update the packet README status line to point at the PR URL once it exists.
  5. Respond to review: expect questions on placement (DPI.lean vs a new file) and
     possible requests to factor the ⊤ cases / p∈{0,1} cases into helper lemmas.

  Reviewer's suggested pre-flight (already green in this packet):
     ./verify.sh <physlib>            # statement / #print axioms / build
     LINT=1 ./verify.sh <physlib>     # + lint_all + lint-style.sh
NEXT
bold "Done."
