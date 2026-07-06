# submissions

A **preparation and staging area** for contributions being prepared for external
projects. Each submission is assembled and self-checked here first, so that when it
is offered upstream, a reviewer can understand and verify it with the least possible
effort.

> **This is not an official submission channel.** Nothing here has been sent to any
> reviewer. For projects with an AI-contribution policy (e.g. PhysLean), all reviewer
> communication — opening the pull request, posting to the forum — is conducted by a
> human, who personally vouches for the work. This repository only *prepares* that
> material.

## Layout

```
submissions/
├── PhysLean/
│   ├── preparation/
│   │   ├── Proof-Joint-convexity-of-the-Umegaki-quantum-relative-entropy/   (PR#0)
│   │   │   ├── README.md    ← start here: what it is, where it fits, how it's checked
│   │   │   ├── PR-BODY.md    ← the pull-request description (for a cold reviewer)
│   │   │   ├── verify.sh     ← one command reproduces every check
│   │   │   ├── proof/        ← the added Lean (excerpt) + the exact patch
│   │   │   ├── paper/        ← the proof as a conventional-maths paper (.qmd → PDF)
│   │   │   ├── test/         ← paper↔Lean fidelity check + literature correspondence
│   │   │   ├── docs/         ← physics brief, conventional writeup, literature
│   │   │   └── evidence/     ← check results + build environment / Lean-run evidence
│   │   └── PR1-Surfaces/     (PR#1 — Cone proved; Torus/Ellipsoid planned, blocked)
│   └── process/              ← the submission-process SRS + traceability + handoffs
│       ├── SRS.md            ← what a submission must satisfy (FR/NFR)
│       ├── traceability.md   ← requirement → evidence map
│       ├── check-srs.sh      ← verifies every traced artifact exists (+ results)
│       └── handoff-torus-ellipsoid.md
└── process/                  ← the verification METHOD, reusable across submissions
    └── verification-method.md
```

Two `process/` scopes, deliberately: the **repo-level** `process/verification-method.md`
is the reusable how-to for the four checks; **`PhysLean/process/`** is the SRS of the
submission process itself, with its traceability map and test results.

## Current submissions

| Project | Submission | Status |
|---|---|---|
| [PhysLean](https://github.com/leanprover-community/physlib) | [PR#0 — Joint convexity of the Umegaki quantum relative entropy](PhysLean/preparation/Proof-Joint-convexity-of-the-Umegaki-quantum-relative-entropy/) | prepared — checks pass; PR not yet opened |
| [PhysLean](https://github.com/leanprover-community/physlib) | [PR#1 — Curved-surface measures](PhysLean/preparation/PR1-Surfaces/) | Cone proved; Torus/Ellipsoid not yet written (blocked on a ruling) |

## How verification works

The method — an increasing-strength ladder of independent checks, with the Lean
kernel's `#print axioms` as the decisive one — is documented once, reusably, in
[`process/verification-method.md`](process/verification-method.md). What a completed
submission must *satisfy* is specified in
[`PhysLean/process/SRS.md`](PhysLean/process/SRS.md), traced to evidence in
[`PhysLean/process/traceability.md`](PhysLean/process/traceability.md).
