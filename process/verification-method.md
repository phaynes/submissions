# Verification method

How a Lean contribution in this repository is checked before it is offered upstream.
The aim is that a reviewer can trust the result with **the least possible effort** —
ideally by running one command and reading a short trace, rather than re-deriving the
mathematics by hand.

The checks form a **ladder of increasing strength**. Each rules out a different way
the work could be wrong. They are ordered so that the cheapest, most decisive checks
come first.

## The four checks

### 1. Statement diff vs master
**Rules out:** a silently *weakened* theorem — proving something easier than the
original open problem and passing it off as the real thing.

We diff the statement being proved against the stub it replaces on `master`. After
removing the proof body and attributes and normalising whitespace, the two must be
**identical** — no hypothesis or conclusion may change; only the proof is new. (This is
a normalised statement match, not a raw byte comparison: formatting and attributes may
differ, the logical statement may not.) This is the first thing to confirm, because
every later check is meaningless if the statement drifted.

### 2. `#print axioms` (the decisive check)
**Rules out:** a hidden `sorry` / `admit` anywhere in the proof **or its entire
dependency chain**.

Lean's `#print axioms <declaration>` reports every axiom the proof ultimately depends
on. A genuine proof shows only the standard foundations —
`[propext, Classical.choice, Quot.sound]`. If any `sorry` were reachable, transitively,
the special axiom `sorryAx` would appear in this list.

This is the **decisive** check: it is a property of the Lean *kernel*, not of any tool
or convention that could be worked around. A clean build alone is not sufficient — the
author remains responsible for the meaning of every statement and proof step — but a
clean `#print axioms` confirms no `sorry`/`admit` is reachable. If you only have time
for one check, this is the one.

### 3. `lake build`
**Rules out:** code that doesn't compile, or that breaks something downstream.

The module — and the library that depends on it — must build green.

### 4. Style lint (`lint_all` / `lint-style`)
**Rules out:** violations of the conventions the project's CI enforces.

The weakest check (style, not correctness), but it is what keeps a PR from bouncing on
mechanical grounds. Reported honestly: a submission states whether it introduces *new*
lint errors, distinct from pre-existing ones already on `master`.

## One command

All four are reproduced by the submission's `verify.sh`:

```bash
./verify.sh /path/to/your/physlib     # checks statement-unchanged, #print axioms, build
LINT=1 ./verify.sh /path/to/your/physlib   # also runs the (slower) full style lint
```

It prints a pass/fail for each check and exits `0` **iff** the mandatory checks pass.

## What this method does *not* claim

- It does not claim the theorem is *useful* or *well-placed* — that is the reviewer's
  judgement, and the submission's writeups exist to inform it.
- It does not hide judgement calls. Where a guideline is only partly met (e.g. PR
  length), the submission **discloses** it rather than burying it.
- Self-reported checks (e.g. "citations checked against arXiv") are labelled as such
  and kept distinct from kernel-verified facts.
