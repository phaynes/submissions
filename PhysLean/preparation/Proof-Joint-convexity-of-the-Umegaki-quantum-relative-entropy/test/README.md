# Proof correspondence — tests

Two questions a reviewer might reasonably ask about the accompanying paper
([`../paper/joint-convexity-proof.qmd`](../paper/joint-convexity-proof.qmd) →
[PDF](../paper/joint-convexity-proof.pdf)):

1. **Does the paper faithfully track the Lean proof** — i.e. is the human-readable
   argument the *same* proof that Lean checks, not a different or hand-wavy one?
2. **How does our proof route relate to the published literature** — is the result and
   its method properly located against what is already known?

These are answered by two artifacts here.

| Test | What it checks | How | Result |
|---|---|---|---|
| [`fidelity-check.sh`](fidelity-check.sh) | Every Lean identifier the paper names as a proof step actually appears in the extracted Lean proof, and vice-versa for the new declarations. | Machine-runnable grep over the paper and `../proof/`. | [`fidelity-results.txt`](fidelity-results.txt) |
| [`literature-correspondence.md`](literature-correspondence.md) | Our α→1⁺ route vs the classical Lindblad/Lieb route — same theorem, documented method, honest differences. | Structured correspondence table sourced from `../docs/literature.qmd`. | in-document |

## 1. Fidelity: paper ↔ Lean

The paper is written to follow the Lean proof "step for step" and carries a
Lean–paper dictionary (§7). `fidelity-check.sh` mechanically confirms that claim: it
extracts the set of Lean identifiers cited in the paper as load-bearing steps
(`sandwichedTraceFunctional_jointly_convex`, `ker_weighted_sum_le`,
`sandwichedRelRentropy.continuousOn`, the new `…_sub_one_div_eventually_le`, the case
labels `h_ev`/`h_lhs`/`h_rhs`, …) and checks each is present in the extracted proof
section `../proof/qRelativeEnt_joint_convexity.lean` (or, for pre-existing inputs,
declared as an external dependency the proof calls). A step named in the paper but
absent from the Lean would be a fidelity gap; a new declaration in the Lean not
explained in the paper would be an exposition gap. The script reports both counts and
exits non-zero if any load-bearing correspondence is missing.

**This is a structural check, not a proof of the proof.** It cannot tell you the
mathematics is *correct* — that is what Lean's kernel does (see
[`../evidence/checks.md`](../evidence/checks.md), check 2). It tells you the paper and
the machine-checked proof are describing the *same* argument, so that reading the
paper is a faithful substitute for reading the Lean.

## 2. Correspondence: literature ↔ our proof

Because joint convexity of the Umegaki entropy is classical (Lindblad 1974, via Lieb's
concavity theorem), there is no single "original paper" whose proof we reproduce: the
published proofs use the classical route, and our formalization deliberately uses the
sandwiched α→1⁺ route instead. [`literature-correspondence.md`](literature-correspondence.md)
sets the two routes side by side and records the three honest observations from the
literature note: the *architecture* is the same (convex one-parameter trace functional
→ limit at the degenerate parameter), the route is assembled from standard published
pieces (Frank–Lieb / Leditzky–Rouzé–Datta / MLDSFT), and it is the same limiting
pattern the library already uses for the sandwiched→Umegaki DPI.
