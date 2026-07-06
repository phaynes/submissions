# PhysLean submission — `qRelativeEnt_joint_convexity`

**This submission aims to close an open `sorry`: joint convexity of the Umegaki quantum relative entropy.**

This directory is the reviewer packet for a single-concept contribution to
[PhysLean](https://github.com/leanprover-community/physlib). It is designed so the
reviewer can understand and verify the work with the least possible effort — one
command reproduces the mandatory checks (set `LINT=1` to also run `lint_all`).

> **Status:** ready for upstream submission — prepared, self-checked, and verified
> against a live Lean toolchain (see [`evidence/lean-run.txt`](evidence/lean-run.txt));
> the pull request has not yet been opened. See the
> [repository README](../../../README.md) for how reviewer contact is handled.

### In this directory

| Path | What it is |
|---|---|
| [`PR-BODY.md`](PR-BODY.md) | The pull-request description, written for a reviewer seeing this cold. |
| [`proof/`](proof/) | The added Lean as an excerpt, plus the exact `+186/−15` patch. |
| [`verify.sh`](verify.sh) | One command that reproduces the mandatory checks; `LINT=1` adds `lint_all` (see §4). |
| [`docs/`](docs/) | Physics brief, conventional-maths writeup, literature comparison (`.qmd` + rendered `.pdf`). |
| [`paper/`](paper/) | The conventional-maths proof as a standalone paper (`.qmd` + `.pdf`), plus [`paper/original/`](paper/original/) recording the classical source (Lindblad 1974). |
| [`test/`](test/) | Fidelity and source-comparison checks that the paper faithfully tracks the Lean proof and the literature. |
| [`evidence/`](evidence/) | Recorded results of each verification check. |
| [verification method](../../../process/verification-method.md) | How the checks work and why (shared across submissions). |

---

## 1. Introduction — what this is

PhysLean's `QuantumInfo` library carried an open `sorry` for inequalities in 
quantum information theory: **joint convexity of the Umegaki quantum relative entropy**,

$$\mathbf{D}\big(p[\rho_1\!\leftrightarrow\!\rho_2]\,\|\,p[\sigma_1\!\leftrightarrow\!\sigma_2]\big)\;\le\;p\,\mathbf{D}(\rho_1\|\sigma_1)+(1-p)\,\mathbf{D}(\rho_2\|\sigma_2).$$

This submission **proves it** (removes the `sorry`), with no new axioms and no
weakening of the statement. The proof route uses the already-proved **joint convexity
of the sandwiched Rényi trace functional** `Q̃_α`
and takes the **α → 1⁺ limit**, in which the sandwiched Rényi relative entropy
converges to the Umegaki relative entropy.

- Physics backgrounder: [`docs/physics-brief.qmd`](docs/physics-brief.qmd)
- Conventional written proof (Lean → paper): [`docs/proof-conventional.qmd`](docs/proof-conventional.qmd)
- Literature comparison: [`docs/literature.qmd`](docs/literature.qmd)

---

## 2. Exactly where the code base changes

Two files change. Net **+186 / −15** lines. **One `sorry` closed, none introduced.**

| File | Change | Why |
|---|---|---|
| `QuantumInfo/Entropy/Relative.lean` | **−15 lines** | The `@[sorryful] theorem qRelativeEnt_joint_convexity := by sorry` (and its `TODO` comment block) is **removed** from where the stub lived. |
| `QuantumInfo/Entropy/DPI.lean` | **+186 lines** | The theorem, now with a full proof, is **added here** — the proof needs the sandwiched-Rényi machinery in `DPI.lean`, and `DPI` imports `Relative`, so proving it in `Relative` would create an **import cycle**. |

**The statement matches the original stub** after removing the proof body and
attributes — no hypothesis or conclusion was changed (only the proof is new). This
is checked automatically by `verify.sh` (§4.1). The theorem is kept a
`theorem` (not `lemma`) because it is a headline result, per PhysLean style.

> **Note for the reviewer on placement:** `DPI.lean` was chosen over a new file
> purely to avoid the import cycle. If you would prefer it in a dedicated file or
> relocated, that is a one-line move — happy to do it.

---

## 3. Types of validation performed

Four independent checks, in increasing strength. All are reproduced by
`./verify.sh <your-physlib-checkout>` (§4).

| # | Check | What it rules out | Result |
|---|---|---|---|
| 1 | **Statement diff vs master** | A silently *weakened* theorem (proving something easier than the original `sorry`) | ✅ matches original stub (proof body + attributes removed; no hypothesis/conclusion changed) |
| 2 | **`#print axioms`** (kernel-level) | A hidden `sorry`/`admit` anywhere in the proof **or its dependency chain** (`sorryAx` would appear) | ✅ `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`** |
| 3 | **`lake build`** of the module | Broken code; downstream breakage | ✅ `QuantumInfo.Entropy.DPI` builds (`Build completed successfully`) |
| 4 | **`scripts/lint-style.sh` / `lint_all`** | Style/convention violations PhysLean CI enforces | ✅ both clean (exit 0). Note the two changed files are on the upstream `LinterExemption.txt`, so `lint-style.sh` does not style-lint them today; run directly, the added lines still add no new `ERR_LIN` |

Check #2 is the strongest: it is a property of the Lean *kernel*, not of any tool that
could be worked around — `#print axioms` reports no `sorryAx`. A clean build alone is
not sufficient; the author remains responsible for the meaning of every statement and
proof step (per `AI-POLICY.md`).

---

## 4. Reproduce the checks with one command

### 4.1 The reviewer script

```bash
# on a physlib checkout switched to branch  feat/qrelent-joint-convexity
./verify.sh /path/to/your/physlib
#   → checks statement-unchanged, #print axioms (no sorryAx), build.
#   → add  LINT=1  to also run lake exe lint_all (slow).
```

It prints a pass/fail for each check and exits 0 iff the mandatory checks pass.
See [`verify.sh`](verify.sh).

---

## 5. SRS trace — submission ⟶ PhysLean review guidelines

Treating PhysLean's [`docs/ReviewGuidelines.md`](https://github.com/leanprover-community/physlib/blob/master/docs/ReviewGuidelines.md)
as the requirement set, each guideline is traced to the evidence that it is met.

| Guideline (requirement) | Evidence in this submission | Status |
|---|---|---|
| **Code quality — correct abstraction** | Reuses `MState`, `Prob`, `Mixable` mixture, the sandwiched-Rényi `Q̃_α`/`D̃_α` API; no new ad-hoc structures. | ✅ |
| **Code quality — correct type theory** | Statement uses `Mixable` mixtures because `ConvexOn` can't be used (`MState` is not an `AddCommMonoid`); the theorem docstring states this. | ✅ |
| **Code quality — no reproving Mathlib** | Builds on existing PhysLean lemmas (`sandwichedTraceFunctional_jointly_convex`, `sandwichedRelRentropy.continuousOn`, `HermitianMat.ker_weighted_sum_le`, …); introduces no re-derivation of library facts. | ✅ |
| **Code quality — concise proofs** | Single theorem; case structure (degenerate → ⊤ → main limit) is minimal; no dead branches. | ✅ |
| **Organization — correct place** | Placed in `DPI.lean` to avoid an import cycle with `Relative.lean` (documented; relocation offered). | ✅ (noted) |
| **Organization — well-defined scope** | One theorem, one concept. | ✅ |
| **Organization — naming/location** | No new files; existing name retained. | ✅ (n/a new file) |
| **Organization — sufficient documentation** | The theorem carries the mathematical intent; this packet adds a conventional writeup + physics brief. | ✅ |
| **Style — `lemma` vs `theorem`** | Kept `theorem` — it is a headline result (the guideline's stated exception). | ✅ |
| **PR & authorship — author understands the material** | Conventional-math writeup + literature comparison in `docs/` demonstrate the argument and its provenance. | ✅ |
| **PR & authorship — single concept** | Exactly one: joint convexity of `𝐃`. | ✅ |
| **PR length** | +186/−15 = **171 net lines → "large PR (100–200)".** Indivisible: it is one theorem's proof and cannot be meaningfully split. Flagged honestly. | ⚠️ noted |
| **Tag system** | Will tag `t-quantumInfo` (or as directed); PR opened non-draft. | ▶ at PR time |

The one ⚠️ (PR length) is disclosed rather than hidden: the proof is a single
logical unit. If the reviewer prefers, the boundary/⊤ cases could in principle be
factored into helper lemmas to shrink the main body — happy to do so on request.

---

## 6. Contents of this packet

```
Proof-Joint-convexity-of-the-Umegaki-quantum-relative-entropy/
├── README.md                     ← this file (intro, change map, validation, SRS trace)
├── verify.sh                     ← one-command reviewer verification
├── PR-BODY.md                    ← the pull-request description, for a reviewer seeing this cold
├── proof/
│   ├── qRelativeEnt_joint_convexity.lean  ← the added Lean, as a standalone excerpt
│   └── qrelent-joint-convexity.patch      ← the exact +186/−15 patch (DPI.lean, Relative.lean)
├── docs/
│   ├── physics-brief.qmd / .pdf  ← why relative entropy + joint convexity matter (for non-experts)
│   ├── proof-conventional.qmd / .pdf  ← the Lean proof rendered as conventional mathematics
│   └── literature.qmd / .pdf     ← comparison to the standard QI literature + citations (arXiv-checked 2026-07-06)
├── paper/
│   ├── joint-convexity-proof.qmd / .pdf  ← the conventional-maths proof as a standalone paper
│   └── original/                 ← provenance of the classical result (Lindblad 1974); PDF intentionally not committed
├── test/                         ← fidelity + source-comparison checks (paper ⟷ Lean ⟷ literature)
└── evidence/                     ← recorded results of each verification check
```

The `docs/*.qmd` and `paper/*.qmd` files render standalone with
`quarto render <file>.qmd`; each is committed alongside its rendered `.pdf`
(rendered 2026-07-06).
