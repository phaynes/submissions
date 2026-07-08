# Partitioning a large Lean file — a reusable design method

**Purpose.** A repeatable, evidence-first method for splitting an over-large Lean file into
correctly-layered concept files, with `QuantumInfo/Entropy/Relative.lean` (2452 lines, 124
declarations) as the worked example. The output is a *design reviewed before any code moves*.

The method is deliberately general: the rest of the codebase (the SQC framework, other
PhysLean contributions) can be restructured with the same steps. It also produces, as a
by-product, the artifact needed for **signature-based discovery of related mathematics** — a
per-declaration dependency graph — so smaller files + this graph compound into a queryable
corpus rather than a text-grep haystack.

---

## The method (six steps)

### Step 1 — Enumerate declarations mechanically
Extract every declaration with `name, kind, privacy, line, length`. Do **not** eyeball it; a
2000-line file has declarations you will miss (this file hid `approxLog`, `ker_kron_*`, and a
whole second analytic engine from a by-eye read). Tool: `harness/lib.sh` `extract_inventory`.

### Step 2 — Extract the real dependency graph
For each declaration's *body*, find which other in-file declarations it references
(word-boundary match against the name set). This yields directed edges
`consumer → provider`. This is ground truth — it is what the code *does*, not what the names
*suggest*. (Result here: 156 edges over 124 nodes.)

### Step 3 — Cluster by cohesion, not by name
Group declarations so that most edges stay *within* a cluster. Name-based bucketing is a
first draft only; the edge data corrects it. The objective is high **cohesion** (intra-cluster
edges) and low **coupling** (inter-cluster edges). Measure both.

### Step 4 — Build the cluster DAG and PROVE it acyclic
Collapse the declaration graph to a cluster graph (one node per candidate file). A file
partition is only *buildable* if this graph is acyclic — Lean forbids cyclic imports. Run a
topological sort. **If it cycles, the partition is invalid** — you must re-home the offending
declarations or merge two clusters. This is the step that catches partitions that would not
compile, before you write a line.

### Step 5 — Adjudicate the back-edges (the human-judgment 10%)
The topological sort surfaces the exact declarations that violate the layering. Each is a
*design decision*, not a mechanical fix: is this lemma really general, or secretly
concept-specific? Does the public theorem live with its concept or its machinery? These are
decided by reading the Lean body, and they are where the design earns its keep. Record each
decision and its rationale.

### Step 6 — Sequence the extraction, gate each step
Order the file creations bottom-up (foundations first). Each extraction is one commit, gated
by the harness (inventory / statement-fidelity / kernel-axioms / elaborated-signatures /
diff-shape / privacy). A red gate ⇒ revert. The endpoint is the full partition; the
per-step evidence is what you show the reviewer so a single final PR is *trusted*, not
re-reviewed.

**Layering rule of thumb** (the invariant behind step 4): a file may only import strictly
lower-layer files — `general math → matrix primitives → the concept's definition → the
concept's API → theorems about the concept`. A reference pointing "up" is the signal a
declaration is mis-placed.

---

## Worked result: `Relative.lean`

### The 7-file target (measured, not sketched)

| File (concept) | decls | ~lines | Nature |
|---|---:|---:|---|
| **A. matrix / Jensen / topology helpers** | 19 | 315 | *general* — Mathlib-upstream candidates (see note) |
| **H. kernel-of-tensor-product lemmas** | 9 | 304 | *general* — Mathlib-upstream candidates |
| **B1. derivative-at-one engine** | 33 | 810 | the α→1 analytic core (`eigenWeight`, `B_of`, …) |
| **BC. approxLog limit + nonnegativity** | 26 | 352 | the α→1 limit argument (merged — see decision 2) |
| **D. `D̃_α` definition + additivity/congruence API** | 14 | 212 | the sandwiched-Rényi concept proper |
| **E. `D̃_α` continuity** | 6 | 136 | public continuity of the family |
| **F. `𝐃` Umegaki relative entropy** | 17 | 291 | **stays in `Relative.lean`** |

Every file lands in the 130–810 line range (vs. one 2452-line file). Only **B1** (810) is
still large — itself a candidate for a later sub-split, but a coherent unit for now.

Contrast the naïve options this pass overturned:
- *2-file split* (the minimum JTS asked): lumps A, H, B1, BC, D, E into one 1491-line
  "sandwiched-Rényi" file — still two-plus concepts in a bucket.
- *by-eye 5-file split*: missed the `approxLog` limit engine and the `kron-kernel` cluster
  entirely, because their names don't announce them.

Only the edge-data pass (steps 2–4) revealed the true structure.

### Cohesion / coupling

- Intra-cluster edges (cohesion): **100** — the clusters are real.
- Inter-cluster edges (coupling): **56** — the boundaries to manage.
- Dominant, correct flow: `A,H → B1 → BC → D → {E, F}` (foundations up to theorems).

### Corrections the pass forced (illustrating step 5)

1. **Engine-internal continuity ≠ family continuity.** `conj_rpow_continuousAt_zero`,
   `B_of_continuousAt` read as "continuity" (cluster E) by name, but they prove continuity of
   *engine internals* and belong in **B1**. Mislabeling them created a false E→B1 back-edge.
2. **`BC` is not separable into "limit" and "nonneg".** `inner_log_sub_log_nonneg` and
   `sandwichedRelRentropy_nonneg` are **mutually recursive** — the approxLog limit and the
   α→1 nonnegativity are one concept and must share a file. A naïve split here would not
   compile.

### OPEN DECISIONS — for review before code (the remaining back-edges)

These two are genuine judgment calls the data isolates but cannot settle; they need a human
reading of the Lean and, for the "general" question, arguably JTS's view:

- **D-OPEN-1 — `sandwichedRelRentropy.continuousAt_1`.** Its body uses `limit_at_one` (a B1
  engine lemma). Does the *public* continuity-at-1 theorem live with its concept (**E**) or
  with the machinery that assembles it (**B1**)? *Recommendation: E* — public API lives with
  the concept; B1 stays private-internal. (It creates a legal E→B1 dependency, not a cycle,
  once the mislabeled internals from correction 1 move to B1.)
- **D-OPEN-2 — `HermitianMat.inner_log_mono_of_psd_of_le`.** Named as a *general* `HermitianMat`
  lemma (cluster A / Mathlib-upstream candidate), but its body depends on entropy-specific
  approxLog lemmas (`inner_log_shift_tendsto`, `posDef_add_eps`). So it is **not** actually
  general as written. *Options:* (a) it stays in the entropy layer (BC), not A — i.e. it is
  mis-named, not mis-placed; or (b) its proof is refactored to remove the entropy dependency,
  making it genuinely general and upstreamable. *Recommendation: (a) for this PR* — do not
  refactor a proof inside a move PR; note (b) as future work.

Resolving these two makes the cluster DAG fully acyclic; the topological order then gives the
file-creation sequence for step 6.

### Note on the "general" clusters A and H (upstreaming)

A (matrix/Jensen/topology) and H (kron-kernel) are **general mathematics, not about entropy**
— they are candidates for Mathlib. **This PR does not move them out of the entropy directory.**
Relocating general lemmas (even within PhysLean to `ForMathlib/`) can break downstream
importers, and that risk is not assessable without visibility into the whole library's usage.
The disciplined stance: keep A and H in place for this PR, *document* them as upstream
candidates, and leave the relocate/upstream call to the maintainer as offered future work.
The two-step convention is: (1) restructure within PhysLean; (2) a separate discrete PR
upstreams the general lemmas to Mathlib.

---

## Reusable artifacts produced

- `harness/` — the extraction + verification toolkit (already Codex-reviewed, self-validated).
- Per-declaration classification: `file, name, kind, privacy, line, length, in-degree, deps`
  (the CSV) — this **is** the graph substrate for signature-based "find related maths" queries.
- The cluster DAG + topological order (JSON).

The same six steps apply to any large file in the corpus. Run once per file; the graph
accumulates into a whole-codebase dependency map.
