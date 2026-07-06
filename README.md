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
│   └── preparation/
│       └── Proof-Joint-convexity-of-the-Umegaki-quantum-relative-entropy/
│           ├── README.md      ← start here: what it is, where it fits, how it's checked
│           ├── PR-BODY.md      ← the pull-request description (for a cold reviewer)
│           ├── verify.sh       ← one command reproduces every check
│           ├── proof/          ← the added Lean (excerpt) + the exact patch
│           ├── docs/           ← physics brief, conventional-maths writeup, literature
│           └── evidence/       ← recorded results of each verification check
└── process/                    ← how the verification is done, and why (reusable)
    └── verification-method.md
```

## Current submissions

| Project | Submission | Status |
|---|---|---|
| [PhysLean](https://github.com/leanprover-community/physlib) | [Joint convexity of the Umegaki quantum relative entropy](PhysLean/preparation/Proof-Joint-convexity-of-the-Umegaki-quantum-relative-entropy/) | prepared — checks pass; PR not yet opened |

## How verification works

The method — an increasing-strength ladder of independent checks, with the Lean
kernel's `#print axioms` as the decisive one — is documented once, reusably, in
[`process/verification-method.md`](process/verification-method.md). Each submission
links to it rather than restating it.
