# Build environment and Lean-run evidence

This records the environment the proof was built in, and the evidence that it compiled.

> **Note.** This file records the *environment* the proof was built in. A freshly
> generated `lake build` + `#print axioms` + lint transcript, produced on a
> Lean-equipped machine against the checkout described below, is in
> [`lean-run.txt`](lean-run.txt). The mandatory checks are also reproduced by
> [`../verify.sh`](../verify.sh); the exact regeneration commands are in §4.

## 1. Toolchain

| | |
|---|---|
| Lean | `leanprover/lean4:v4.31.0` (pinned in `lean-toolchain`) |
| Mathlib | `v4.31.0` — resolved rev `fabf563a7c95` |
| Build system | Lake (manifest version 1.2.0) |
| Package | `Physlib` (targets `Physlib`, `QuantumInfo`); lib built with `-Dwarn.sorry=false -Dweak.says.verify=true` |

Resolved dependency revisions (from `lake-manifest.json`):

| Package | Rev |
|---|---|
| mathlib | `fabf563a7c95` |
| batteries | `fa08db58b30e` |
| aesop | `e3cb2f741431` |
| Qq | `f46324995fca` |
| proofwidgets | `24b0d9dc081c` |
| importGraph | `5c7542ed018c` |

## 2. Host

| | |
|---|---|
| OS | macOS 26.5.1 |
| Architecture | arm64 (Apple silicon) |

## 3. Build artifact (evidence of a successful compile)

Lean only emits a `.olean` when the source compiles and its proofs are accepted by the
kernel. The presence of this artifact is direct evidence that `DPI.lean` — the file
containing `qRelativeEnt_joint_convexity` and its supporting lemmas (the majorant
`…_sub_one_div_eventually_le`, the mixture lemmas, and the `α → 1⁺` continuity lemma) —
compiled successfully. The size/hash below are for a specific local build of commit
`f901e353` and are machine-specific (`.olean`s are not bit-reproducible across machines);
the portable evidence is the `#print axioms` check in [`checks.md`](checks.md) /
[`lean-run.txt`](lean-run.txt).

| | |
|---|---|
| File | `.lake/build/lib/lean/QuantumInfo/Entropy/DPI.olean` |
| Size | 323,656 bytes |
| Modified | 2026-07-07 19:21 (local) |
| SHA-256 | `b17f5bc6b1beab638da51742c254669c27e2613606fba0a687a91ab38220a42c` |

Provenance of the source it was built from:

| | |
|---|---|
| Commit | `f901e3534f35702ff1db999bebf97cbc8611f858` |
| Author | Philip Haynes |
| Date | 2026-07-07 18:37:17 +1000 |
| Subject | `feat(QuantumInfo): prove qRelativeEnt_joint_convexity (joint convexity of Umegaki relative entropy)` |
| Signed-off-by | Philip Haynes |
| Co-authored-by | Helios; Claude Opus 4.8; Codex gpt-5.5 (AI assistance, disclosed per `AI-POLICY.md`) |

(The artifact's mtime precedes the commit time by a few minutes: the file was compiled
during development, then committed — the ordinary order of events.)

## 4. Regenerating a fresh transcript

On a machine with the toolchain installed (`elan` will fetch `v4.31.0` from
`lean-toolchain` automatically), from a `physlib` checkout on the proof branch:

```bash
# 1. Build the module (fetches/builds Mathlib on first run — can be lengthy)
lake build QuantumInfo

# 2. The decisive check: no hidden sorry anywhere in the dependency chain
echo 'import QuantumInfo.Entropy.DPI
#print axioms qRelativeEnt_joint_convexity' > /tmp/axioms.lean
lake env lean /tmp/axioms.lean
#   expected: 'qRelativeEnt_joint_convexity depends on axioms:
#              [propext, Classical.choice, Quot.sound]'   — no sorryAx

# 3. Or run all mandatory checks at once:
../verify.sh /path/to/your/physlib
```

Capturing the stdout of steps 1–2 into `evidence/lean-run.txt` gives the fresh transcript.
Its expected content (the axiom list, no `sorryAx`) is already recorded in
[`checks.md`](checks.md) and the commit message of `f901e353`.
