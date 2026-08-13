# SRS - PR2 SandwichedRenyi Submission Process

This software/process requirements specification defines what it means for the
PR2 sandwiched-Renyi split packet to be ready for an external PhysLean pull
request.

The requirements combine:

- PhysLean `docs/ReviewGuidelines.md`;
- PhysLean `AGENTS.md`;
- PhysLean `AI-POLICY.md`;
- PhysLean `scripts/README.md`;
- Mathlib-style linting as inherited through `scripts/lint-style.py`;
- the PR2-specific pure-refactor harness.

Each requirement is traced in `process/traceability.md`.

## Functional Requirements

### FR-PR2-001 - Concept boundary

The submission SHALL separate the sandwiched Renyi family `D̃_α` from the
Umegaki relative entropy API `qRelativeEnt` / `𝐃`.

### FR-PR2-002 - Statement preservation

The submission SHALL preserve public theorem statements except for explicitly
whitelisted and reviewed public-surface movement.

### FR-PR2-003 - Wrapper equivalence

The theorem `qRelativeEnt.lowerSemicontinuous` SHALL retain its normalized Lean
type and SHALL delegate to a sandwiched alpha-equals-one boundary theorem.

### FR-PR2-004 - Privacy restoration

The eigen-weight implementation helpers SHALL resolve as private declarations in
`SandwichedRenyi.lean`.

### FR-PR2-005 - Import acyclicity

The module graph SHALL remain acyclic, with `Relative.lean` importing
`SandwichedRenyi.lean` and not the other way around.

### FR-PR2-006 - Kernel validation

The submission SHALL pass affected-module builds, PR2 harness checks,
axiom/signature checks, and full `lake build`.

### FR-PR2-007 - Standards conformance

The submission SHALL account for PhysLean/Mathlib-style coding standards. Any
known partial style conformance SHALL be explicit and justified rather than
hidden.

### FR-PR2-008 - Reviewer packet

The submission SHALL include a plain-English PR body, reviewer map, physics
brief, methodology brief, verification script, and recorded evidence.

### FR-PR2-009 - AI policy disclosure

The PR body SHALL disclose AI assistance and leave all reviewer communication and
final submission responsibility with the human author.

## Non-Functional Requirements

### NFR-PR2-001 - Evidence first

Claims about equivalence, privacy, imports, and proof validity SHALL cite Lean,
Varro, harness, build, or review evidence.

### NFR-PR2-002 - Single-concept scope

The PR SHALL remain a refactor of the sandwiched Renyi relative entropy file
boundary, not a proof-golf, style-normalization, theorem-renaming, or Mathlib
upstreaming PR.

### NFR-PR2-003 - Reviewer speed

The packet SHOULD let a reviewer understand the motivation, risk, and checks in
one pass without reading Helios project internals.

### NFR-PR2-004 - Reproducibility

The packet SHOULD provide one command to replay the mandatory checks on a local
PhysLean checkout.
