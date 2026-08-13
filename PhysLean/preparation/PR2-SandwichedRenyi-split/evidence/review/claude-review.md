## Review: PR2 V2 Proof Refactor — Findings First

**No blocking findings.** The refactor is a sound, best-practice Lean proof-organization move. The evidence is internally consistent with the source, and I found nothing that should stop final equivalence validation. Details and a few non-blocking notes follow.

### Verification performed (read-only)

- **No import cycle.** `SandwichedRenyi.lean` imports only `VonNeumann` + `Physlib.Meta.Sorry`; `Relative.lean` `public import`s `SandwichedRenyi` (line 9). The dependency direction is one-way and matches the intended ownership (`qRelativeEnt` wraps `D̃_1`). ✔
- **Privatization is safe.** `eigenWeight`, `inner_cfc_eq_sum_eigenWeight`, `eigenWeight_nonneg`, `eigenWeight_zero_of_eigenvalue_zero` are now `private` and all consumers (`inner_cfc_approxLog_ge`, `tendsto_inner_cfc_approxLog`, the `lowerSemicontinuous_2` section, etc.) live in the *same module*. A repo-wide grep found **zero** external consumers of these helpers. ✔
- **Moved public theorems have no external users.** `inner_log_bounded_near` (1556) and `qRelativeEnt_lowerSemicontinuous_2` (1684) are referenced only inside `SandwichedRenyi.lean` (by `sandwichedRelRentropy_one_lowerSemicontinuous` at 1736/1747). Moving files cannot break any downstream import. ✔
- **Boundary theorem is well-formed.** `sandwichedRelRentropy_one_lowerSemicontinuous` (1725) is stated purely over `D̃_1(ρ‖σ)` / `SandwichedRelRentropy 1`, carries `@[fun_prop]`, and its full α=1 case-split proof is self-contained. The Varro decl snapshot confirms it resolves as a theorem depending on `inner_log_bounded_near` and `qRelativeEnt_lowerSemicontinuous_2` (i.e. it actually compiled, referencing the now-`_private...eigenWeight` symbols). ✔
- **Wrapper preserves the statement.** `qRelativeEnt.lowerSemicontinuous` (Relative 97–98) keeps its `@[fun_prop]` attribute and identical type; the proof is the one-line `simpa [qRelativeEnt] using sandwichedRelRentropy_one_lowerSemicontinuous`, which is exactly `qRelativeEnt ρ σ ≝ D̃_1(ρ‖σ)` unfolded. The V2 decl snapshot's `type` field matches the wrapper statement and now lists `sandwichedRelRentropy_one_lowerSemicontinuous` as a dependency. ✔
- **Evidence ↔ source consistency.** The report's "public surface delta" (Relative loses the two helpers; Sandwiched gains three; eigenWeight family removed from public facts and now resolves as `_private.QuantumInfo.Entropy.SandwichedRenyi.0.eigenWeight`) matches what the source and the `decl-eigenWeight.json` snapshot show. ✔

`★ Insight ─────────────────────────────────────`
- In Lean 4's module system, `public import` re-exports names, so even if a downstream file *had* used `inner_log_bounded_near` via `Relative`, moving it to `SandwichedRenyi` would remain transparent — but confirming zero consumers makes the move risk-free rather than merely convenient.
- The refactor removes an *abstraction leak*: V1 forced eigen-weight internals public purely so a proof in the wrong file could compile. Re-privatizing them is the real value here — the public surface now reflects genuine API, not compile-time plumbing.
- `@[fun_prop]` on the boundary theorem means `fun_prop` can discharge sandwiched-α=1 LSC goals directly, not only the `qRelativeEnt`-phrased ones — a small capability gain, not a behavior change.
`─────────────────────────────────────────────────`

### Answers to the four questions

1. **Better ownership boundary?** Yes. The α-family machinery (eigen-weight expansion, `approxLog`, both LSC sections) now lives with `SandwichedRelRentropy`, and `Relative` reduces to a wrapper. This is the correct direction given `qRelativeEnt := D̃_1` and the existing import edge.
2. **Acceptable that the two helper theorems move files but keep statements?** Yes — statements unchanged, no external consumers, still public and re-exported. Behaviorally invisible.
3. **Is `sandwichedRelRentropy_one_lowerSemicontinuous` an appropriate boundary theorem?** Yes — stated in the sandwiched vocabulary, `@[fun_prop]`, self-contained proof, cleanly consumed by the wrapper.
4. **Import-cycle / API / naming / reviewer-risk problems?** None blocking. See notes below.

### Non-blocking notes (optional polish, not gates)

- **Naming inconsistency (minor):** `qRelativeEnt_lowerSemicontinuous_2` now lives in `SandwichedRenyi.lean` but keeps a `qRelativeEnt`-prefixed name, out of step with the module's `sandwichedRelRentropy_*` family. Its statement is also phrased with `⟪ρ.M, ρ.M.log - x'.M.log⟫` (the relative-entropy expansion), so the name isn't nonsensical — but for discoverability it reads as a Relative-file lemma stranded in the sandwiched file. Consider renaming (e.g. `sandwichedRelRentropy_one_lowerSemicontinuous_aux`) if PR2 isn't required to preserve the exact V1 public name.
- **Public-surface hygiene (minor):** `inner_log_bounded_near` is a generic public name, and both it and `qRelativeEnt_lowerSemicontinuous_2` are genuinely internal (zero external users). The design deliberately keeps them public; if preserving the V1 surface isn't a hard requirement, they could be made `private` too, shrinking the exported API further. Purely optional.
- **Validation reminder (procedural, not a defect):** pre-review evidence only builds the two modules in isolation. Since re-privatization changes visibility, the deferred **full build** is the right gate to confirm no downstream module implicitly relied on the old public eigen-weight names — my grep says none do, but the full build is the authoritative check. The gating as described is appropriate.

**Recommendation:** proceed to final equivalence / full-build / harness validation. No changes required first.
