# Build environment and Lean-run evidence

This records the environment the proof was built in, and the evidence that it compiled.

> **Honesty note.** The evidence below is a **recorded past build** — the on-disk build
> artifact (`.olean`) produced when the proof was developed. A *freshly generated*
> `lake build` + `#print axioms` transcript is **not** included here, because the machine
> assembling this packet does not have the Lean toolchain (`lake`/`elan`) installed. The
> exact commands to regenerate a fresh transcript on a Lean-equipped machine are in §4;
> the mandatory checks are also reproduced by [`../verify.sh`](../verify.sh).

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
containing `qRelativeEnt_joint_convexity` and the new `…_sub_one_div_eventually_le`
lemma — compiled successfully.

| | |
|---|---|
| File | `.lake/build/lib/lean/QuantumInfo/Entropy/DPI.olean` |
| Size | 323,656 bytes |
| Modified | 2026-07-03 09:11 (local) |
| SHA-256 | `bcabba167208fea60e62b69b512f020bb8ccaef5201bb4d6b60a9a864841496e` |

Provenance of the source it was built from:

| | |
|---|---|
| Commit | `bb18f8dc7833d18485cf66a0fd2846132267de57` |
| Author | Philip Haynes |
| Date | 2026-07-03 09:15:34 +1000 |
| Subject | `feat(QuantumInfo): prove qRelativeEnt_joint_convexity (joint convexity of Umegaki relative entropy)` |

(The artifact's mtime precedes the commit time by a few minutes: the file was compiled
during development, then committed — the ordinary order of events.)

## 4. Regenerating a fresh transcript

On a machine with the toolchain installed (`elan` will fetch `v4.31.0` from
`lean-toolchain` automatically), from a `physlib` checkout on the proof branch:

```bash
# 1. Build the module (fetches/【builds Mathlib on first run — can be lengthy)
lake build QuantumInfo.Entropy.DPI

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
[`checks.md`](checks.md) and the commit message of `bb18f8dc`.
