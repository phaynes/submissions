# Yaqin Tooling Process For PhysLean Submissions

Working tool name: **Yaqin**.

This process note separates the concise pull-request submission from the larger
evidence package used to justify high-integrity Lean refactors.

## Purpose

For maintenance refactors, the goal is not to ask a reviewer to trust an
individual developer or an AI assistant. The goal is to make the transformation
mechanical and auditable:

```text
checked Lean source
-> Lean-derived declaration/proof graph
-> formal refactor constraints
-> convention-based module partition
-> mechanical move
-> preservation certificate
-> concise PR plus evidence package
```

The AI client operates the process. Lean and Varro provide the authority.

## PR Submission Versus Evidence Package

| Artifact | Audience | Content |
|---|---|---|
| PR body | PhysLean reviewer | Short motivation, changed files, public API deltas, checks run, evidence-package pointer. |
| Evidence package | Reviewer or maintainer who wants the audit trail | Graph, partition policy, preservation contract, equivalence/faithfulness report, axiom/privacy reports, replay commands, literature/physics brief. |

The PR body should remain conventional and concise. The evidence package should
show the method.

## Installation Target

The intended Yaqin installation path is:

1. install the local background service;
2. register Lean workspaces such as PhysLean and Mathlib;
3. register the submission workspace;
4. connect AI clients through the service capability handshake;
5. run Varro/Lean queries rather than text scraping;
6. generate/update PR and evidence artifacts.

The first target platform is macOS. Linux follows once the service interface is
stable.

## Refactor Preservation Contract

Each submission refactor should provide a contract covering:

- public declaration survival;
- elaborated public type preservation;
- axiom/sorry surface preservation;
- privacy minimization;
- import acyclicity;
- dependency-direction correctness;
- concept ownership rules;
- explicit whitelist of intentional deltas;
- full `lake build`.

The process should make disagreement precise. Maintainers can argue about the
contract and whitelisted deltas, not about whether an unstructured edit silently
changed the mathematics.

## Reviewer Experience

A reviewer should be able to:

1. read the concise PR;
2. inspect the module/dependency diagram;
3. inspect the intentional delta table;
4. run one replay command;
5. optionally inspect the full graph and preservation certificate.

The desired effect is that safe refactoring becomes a repeatable engineering
process, not a matter of personal proof-code heroics.

## PR2 Application

For PR2, the current two-file split is Phase 1 evidence. The final architecture
should be graph-derived and convention-constrained. Yaqin should be used to
show:

- why the sandwiched Renyi material should leave `Relative.lean`;
- how the finer module partition follows Lean dependencies and conventions;
- which public theorem statements are preserved;
- which deltas are intentional;
- why the final module graph is acyclic;
- how the literature and physics explanation remain linked to the formal proof.
