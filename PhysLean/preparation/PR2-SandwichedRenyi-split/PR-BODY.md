# Pull Request Body

**Title**

```text
refactor(QuantumInfo): split sandwiched Renyi relative entropy into its own file
```

**Body**

```markdown
This refactors the `QuantumInfo` entropy layer by moving the sandwiched Renyi
relative entropy family `D̃_α` from `QuantumInfo/Entropy/Relative.lean` into the
new concept file `QuantumInfo/Entropy/SandwichedRenyi.lean`.

The Umegaki quantum relative entropy `qRelativeEnt`, notation `𝐃`, remains in
`Relative.lean`, where it is definitionally the alpha-equals-one specialization
of the sandwiched family:

    qRelativeEnt ρ σ := D̃_1(ρ‖σ)

## Why this refactor

`Relative.lean` had grown into a mixed file: it contained both the full
sandwiched Renyi analytic engine and the Umegaki-relative-entropy API. This made
the dependency direction hard to see. The new organization is:

- `SandwichedRenyi.lean`: definition and API for `D̃_α`, including the spectral
  proof machinery, additivity, continuity, congruence, nonnegativity, and the
  alpha-equals-one lower-semicontinuity theorem;
- `Relative.lean`: the Umegaki-facing `qRelativeEnt` API and wrappers over
  `D̃_1`.

This matches the mathematical ownership: `𝐃` is the `α = 1` specialization of
the sandwiched family, so `Relative.lean` should depend on the sandwiched file,
not force sandwiched proof internals to be public.

## Important proof-organization change

The proof graph showed that `qRelativeEnt.lowerSemicontinuous` depended on
spectral/eigen-weight internals from the sandwiched analytic engine. In the first
split this would have forced these helpers to be public:

- `eigenWeight`
- `inner_cfc_eq_sum_eigenWeight`
- `eigenWeight_nonneg`
- `eigenWeight_zero_of_eigenvalue_zero`

The final refactor instead moves the alpha-equals-one lower-semicontinuity proof
into `SandwichedRenyi.lean` and exposes one boundary theorem:

    sandwichedRelRentropy_one_lowerSemicontinuous

Then `qRelativeEnt.lowerSemicontinuous` remains the same public theorem but is
proved by:

    simpa [qRelativeEnt] using sandwichedRelRentropy_one_lowerSemicontinuous

This lets the eigen-weight helpers become private implementation details again.

## Public API drift

Expected public-surface movement:

- `Relative.lean` no longer exports:
  - `inner_log_bounded_near`
  - `qRelativeEnt_lowerSemicontinuous_2`
- `SandwichedRenyi.lean` now exports:
  - `inner_log_bounded_near`
  - `qRelativeEnt_lowerSemicontinuous_2`
  - `sandwichedRelRentropy_one_lowerSemicontinuous`
- The eigen-weight helper family is no longer public and resolves as private
  declarations in `SandwichedRenyi.lean`.

The statement of `qRelativeEnt.lowerSemicontinuous` is unchanged. The validation
report records identical normalized type hashes before and after the refactor.

## Reviewer map

Suggested review order:

1. `QuantumInfo.lean`: import order.
2. `QuantumInfo/Entropy/SandwichedRenyi.lean`: moved sandwiched family and
   boundary theorem.
3. `QuantumInfo/Entropy/Relative.lean`: reduced Umegaki wrapper surface.
4. `qRelativeEnt.lowerSemicontinuous`: unchanged statement, wrapper proof.
5. `scripts/LinterExemption.txt`: new large moved file is exempted consistently
   with the current QuantumInfo style-lint migration state.

## Checks

The submission packet includes a replay script and evidence. The final checks
passed:

```bash
lake build QuantumInfo.Entropy.SandwichedRenyi
lake build QuantumInfo.Entropy.Relative
/path/to/PR2-SandwichedRenyi-split/harness/20_check.sh
/path/to/PR2-SandwichedRenyi-split/harness/20_check.sh --axioms
lake build
./scripts/lint-style.sh
```

The PR2 harness checks declaration inventory, statement hashes, privacy drift,
diff shape, public theorem axiom surface, and elaborated kernel signature
fidelity. The full build succeeds; the only warning observed is the pre-existing
unused simp argument in `Physlib/Electromagnetism/Kinematics/EMPotential.lean`.

## AI assistance

Developed with AI assistance. I have reviewed the theorem statements, refactor
boundary, proof-graph evidence, and validation output, and I take responsibility
for the submission under `AI-POLICY.md`.

Optional supporting packet:

<link to this preparation/submission packet once pushed>
```

## Optional Reviewer Comment

```markdown
Optional supporting material for this refactor is available here:

<link to packet once pushed>

It contains:

- a plain-English refactor brief;
- a physics/mathematics explanation of why `𝐃` is the alpha-equals-one wrapper
  over the sandwiched Renyi family;
- the PR2 harness and final validation report;
- Claude review of the proof-graph-guided V2 refactor;
- an SRS and traceability map against PhysLean/Mathlib-style standards.

The intended review path is still the Lean diff and the checks listed in the PR
body. The packet is there to make the methodology and evidence easy to audit.
```
