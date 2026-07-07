# Axiom surface — the 4 conditional assumptions

The SQT proof product is **conditional on exactly these 4 Lean `axiom` declarations**.
Everything else in the 11 modules is proved (no `sorry`, no `admit`). This file is the
honest statement of what the proof assumes; the machine source of truth for the count is
`sqc-proof-framework/control/boundary.json` (`axioms: 4`).

Three of the four are **accepted paper-level physics assumptions** with citations; the
fourth is a **rescoped-after-refutation** assumption that is a real theorem on its stated
domain. None is known-false (a previously-false one was removed — see §5).

---

## PinchingEntropy.lean — 1 axiom

### `relative_entropy_jointly_convex`
Joint convexity of the quantum relative entropy, **on-support**. This is Lieb's theorem
(Lieb–Ruskai 1973, DOI 10.1063/1.1666274) restricted to the support condition
`supp ρ ⊆ supp σ`, where the relative entropy is the honest quantity.

**Why it is an axiom here, not a proof:** the *unconditional* form is **false** in this
development's encoding (junk `log 0 = 0`), and that was proved — see
`not_relative_entropy_jointly_convex_unconditional` in the module, with the
kernel-verified counterexample `ρ₁ = ρ₂ = σ₁ = |0⟩⟨0|`, `σ₂ = |1⟩⟨1|`, `p = 1/2`, which
forces `log 2 ≤ 0`. The axiom is the *true* on-support restriction.

> **Connection to the PhysLean work:** this on-support joint convexity is exactly the
> theorem `qRelativeEnt_joint_convexity` proved and submitted upstream in PhysLean PR
> #1378. Discharging this axiom against that PhysLean result (once merged) is the natural
> way to remove it from this surface — a concrete axiom-reduction target.

---

## SQT_Axiom.lean — 3 axioms

### A3-support: `gkls_evolution`
The existence of a GKLS (Lindblad) time-evolution map. Currently stated over an
**unconstrained** generator — flagged in-code as *sound-but-weak* (trivially inhabited).
Strengthening means giving the generator a real defining law (semigroup / master
equation); noted as future work, not a false-axiom.

### A3: `spohn_entropy_production`
Spohn's entropy-production inequality: entropy production `≥ 0` for **unital GKLS**
evolution with `t > 0`. Paper assumption — Spohn (1978), DOI 10.1063/1.523789. Restricted
to unital dynamics deliberately (the unrestricted form is not assumed).

### A3: `entropy_monotone_gkls`
Monotonicity companion to Spohn under the same unital-GKLS hypotheses. Rests, like
`spohn_entropy_production`, on `gkls_evolution`; the two are expected to collapse to one
lemma once the generator has a real defining law.

---

## The two paper-level assumptions imported elsewhere

Two of the framework's four "principal paper assumptions" (per the framework README) are
**not** bare axioms in the modules above but are carried as interface/bridge assumptions:

- **A1 Stinespring dilation** — every CPTP map has a unitary dilation. Stinespring (1955),
  DOI 10.1090/S0002-9939-1955-0069403-4. (`stinespring_exists` was *discharged to a
  theorem* in the Fable audit; it is no longer a bare axiom.)
- **A2 Strong subadditivity** — `S(AB) + S(BC) ≥ S(ABC) + S(B)`. Lieb–Ruskai (1973).
- **A4 SQC target** — the Barandes correspondence, now exposed as the concrete
  `Quantum.SQC.SQCorrespondence` interface with two checked instances (a two-state swap and
  a non-permutation 3-4-5 rotation), **not** a bare existential axiom.

---

## §5 — What was removed (why "no known-false axiom" is a real claim)

The current 4-axiom surface is what remains after aggressive reduction (the framework
README records "reduced from 72"). Specifically, false/misstated assumptions were removed:

- `relative_entropy_jointly_convex` **unconditional** → refuted and rescoped to on-support
  (the axiom above), with a kernel-verified counterexample kept in the module.
- `relative_entropy_pinching_eq_entropy_diff` and `max_entropy_at_fixed_energy` — deleted
  (2026-07-02).
- `relative_entropy_gibbs_identity` — restated with `β > 0`.
- `stinespring_exists` — discharged to a theorem.

`control/boundary.json` reports `flagged_false_or_misstated: []`.
