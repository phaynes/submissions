# Literature correspondence — classical route vs the route we formalized

Joint convexity of the Umegaki relative entropy is a **classical** result (Lindblad
1974), so there is no single "original paper" whose proof this contribution reproduces.
The published proofs use one route; the Lean formalization deliberately uses another.
This note sets them side by side and records the honest differences. It is a
correspondence argument, not an automated test — its "result" is the documented
conclusion at the end. Sourced from [`../docs/literature.qmd`](../docs/literature.qmd).

## The two routes

| | Classical route (the literature) | Route formalized here |
|---|---|---|
| **Origin** | Lindblad 1974 [Lindblad74]; modern exposition Carlen [Carlen10]. | Assembled from Frank–Lieb [FrankLieb13] / Leditzky–Rouzé–Datta [LRD17] + MLDSFT [MLDSFT13]. |
| **Convex functional** | Lieb's WYD functional $(A,B)\mapsto\operatorname{Tr}[K^\dagger A^s K B^{1-s}]$, jointly concave [Lieb73]. | Sandwiched trace functional $\widetilde Q_\alpha$, jointly convex for $\alpha>1$. |
| **Limit taken** | Degenerate parameter $s\to 1$, where the functional reduces to a trace and its derivative yields the logarithms. | $\alpha\to 1^{+}$, where $\widetilde D_\alpha\to D$ (Umegaki). |
| **Mechanism at the limit** | Derivative (differentiate the one-parameter family at the degenerate value). | One-sided **convergent majorant** — no differentiability; needs only continuity + two scalar bounds. |
| **Matrix-analysis engine** | Lieb concavity [Lieb73]. | Same family: Lieb–Ando trace concavity [Lieb73; Ando79], via `HermitianMat.trace_conj_rpow_concave`. |

## Three honest observations

1. **The architecture is identical.** Both routes are: *a jointly convex/concave
   one-parameter trace functional* → *a limit at the degenerate parameter value, where
   the relative entropy emerges*. Our proof is the **sandwiched analogue** of Lindblad's
   argument, with $\widetilde Q_\alpha$ in place of the WYD functional and a convergent
   majorant in place of the derivative.

2. **The route is standard pieces, but not the textbook route to _this_ theorem.**
   Joint convexity of the Umegaki entropy predates the sandwiched family by four decades,
   so textbooks prove it classically. The α→1⁺ transfer we use is itself standard — it is
   exactly how the sandwiched DPI gives the Umegaki DPI [MLDSFT13; Wilde17], and how the
   PhysLean library already proves `sandwichedRenyiEntropy_DPI_eq_one`. We apply the same
   established pattern to joint convexity.

3. **Why this route, in Lean.** The classical route would require formalizing Lieb's WYD
   concavity and a differentiation-at-the-degenerate-value argument from scratch. The
   sandwiched route reuses machinery **already in the library** (the Frank–Lieb
   variational proof of $\widetilde Q_\alpha$ convexity, and continuity of
   $\widetilde D_\alpha$), so the only genuinely new mathematics is the convergent
   majorant (Lemma E). This is a formalization-economy choice, disclosed as such.

## Result

The formalized theorem is the **same statement** proved in the classical literature, by
a **documented, published-in-pieces** route that is the sandwiched-Rényi analogue of the
classical argument. The route differs from the textbook proof in its choice of
one-parameter functional and in replacing a derivative with a convergent majorant; both
differences are deliberate, standard, and disclosed. No step depends on an unpublished or
ad-hoc ingredient: every input is either a cited theorem or the one new elementary lemma
(E), whose own proof uses only `log x ≤ x−1` and `|eˣ−1−x| ≤ x²`.

## References

Full bibliographic detail (including the arXiv-checked eprint corrections, e.g.
Beigi = arXiv:1306.5920, LRD = arXiv:1604.02119) is in
[`../docs/literature.qmd`](../docs/literature.qmd).
