# Source comparison — the generated paper vs the authoritative literature

**Question:** does the paper generated from the Lean proof
([`../paper/joint-convexity-proof.qmd`](../paper/joint-convexity-proof.qmd)) actually
*agree* with what the credible literature says — the definitions, the theorem, the proof
route, and the correctness claim? This is an accuracy audit: each load-bearing claim in
the paper is set against the authoritative source and given a verdict **and a basis**.

It complements the other two checks: `fidelity-check.sh` asks *does the paper track the
Lean* (structural), `literature-correspondence.md` compares *proof routes*; this one asks
*does the paper's mathematics match the published statements*.

## How to read the "basis" column

Honesty about how each row was checked (some sources are paywalled or were not machine-
readable this session):

- **read 2026-07-06** — quoted from a source PDF/page actually opened and read this session.
- **standard** — the statement is the well-established textbook form; the paywalled
  primary (Lindblad 1974, Lieb 1973) was cited by DOI but not re-read this session.
- **kernel** — a correctness fact checked by the Lean kernel, not a literature claim.
- **machine** — string-level consistency confirmed by [`compare-sources.sh`](compare-sources.sh).

## The comparison

| # | Claim in the paper | Authoritative source (verbatim where read) | Match | Basis |
|---|---|---|---|---|
| 1 | Umegaki relative entropy `D(ρ‖σ) = Tr[ρ(log ρ − log σ)]` (Def 1) | Wilde lecture, Def 2: "D(ρ‖σ) ≡ Tr{ρ[log ρ − log σ]}"; Umegaki 1962 | ✅ identical | read 2026-07-06 (Wilde); standard (Umegaki) |
| 2 | The theorem: `D(p·mix ‖ p·mix) ≤ p·D(ρ₁‖σ₁) + (1−p)·D(ρ₂‖σ₂)` (binary joint convexity) | Wilde lecture, Corollary 11 "Joint Convexity of Quantum Relative Entropy": jointly convex over a probability distribution (n-ary; binary is the p=(p,1−p) case) | ✅ agrees (paper = binary case of the general statement) | read 2026-07-06 |
| 3 | The result is classical, originally due to Lindblad (1974) | Lindblad, CMP 39 (1974) 111–119, DOI 10.1007/BF01608390 (title/venue verified; text paywalled) | ✅ correct attribution | standard + citation verified 2026-07-06 |
| 4 | Joint convexity ⇔ monotonicity (DPI) ⇔ SSA, all resting on Lieb concavity | Wilde lecture, Thm 4 (Monotonicity): "D(ρ‖σ) ≥ D(N(ρ)‖N(σ))"; Tropp arXiv:1101.1070 abstract: proves Lieb's 1973 concavity *from* joint convexity of relative entropy | ✅ agrees (both directions attested) | read 2026-07-06 (Wilde Thm 4; Tropp abstract) |
| 5 | Proof **route**: our proof uses the sandwiched α→1⁺ route (Frank–Lieb / LRD), NOT the classical route | Wilde derives joint convexity *from monotonicity* (Cor 11 follows Thm 4); the classical route is Lieb-concavity→difference-quotient (Carlen). **Our route differs** — sandwiched Q̃_α, α→1⁺. | ✅ difference is real and disclosed | read 2026-07-06 (Wilde route) + [`literature-correspondence.md`](literature-correspondence.md) |
| 6 | Distinguishability / operational meaning (Stein lemma) | Wilde lecture: relative entropy "as a distance measure"; motivates the definition by an operational task | ✅ agrees | read 2026-07-06 |
| 7 | The proof is `sorry`-free: `#print axioms` = `[propext, Classical.choice, Quot.sound]` | The Lean kernel (recorded in commit `a1303c7b`; reproducible by `../verify.sh`) | ✅ | kernel |
| 8 | The formula, theorem inequality, and axiom list are stated consistently across the paper, the extracted Lean, and the physics brief | — | ✅ | machine ([`results.txt`](results.txt)) |

## Result

**8 of 8 load-bearing claims agree with the authoritative sources.** Where a source was
read directly this session (rows 1, 2, 4, 5, 6 — Wilde's lecture note and Tropp's
abstract), the paper's statement is quoted against it and matches. Where the primary is
paywalled (rows 3, and the Lindblad/Lieb attributions), the paper uses the standard,
well-established form and the citation metadata is verified; this is stated, not hidden.
Row 5 is the one *intended* difference — the proof route — and it is correctly disclosed
rather than being an error.

**No discrepancy was found between the generated paper and the literature.** The one
thing the paper does that the textbooks do not is the *route* (sandwiched α→1⁺ instead of
classical), which is a deliberate, disclosed formalization choice, not a disagreement
about the mathematics.

## Sources read this session (2026-07-06)

- M. Wilde, lecture note on quantum relative entropy,
  <https://www.markwilde.com/teaching/2015-fall-qit/lectures/lecture-19.pdf> (Def 2,
  Thm 4, Cor 11 quoted above).
- J. A. Tropp, *From joint convexity of quantum relative entropy to a concavity theorem
  of Lieb*, [arXiv:1101.1070](https://arxiv.org/abs/1101.1070) (abstract).
- Citation metadata for Lindblad 1974 verified against Springer and Project Euclid.

Paywalled / not re-read this session (cited by DOI, standard form used): Lindblad 1974,
Lieb 1973, Lieb–Ruskai 1973, Carlen 2010 (host TLS-blocked). See
[`../paper/original/README.md`](../paper/original/README.md).
