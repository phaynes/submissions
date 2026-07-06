# SRS — the submission-preparation process

**Software / process requirements specification** for preparing a formal-mathematics
contribution for external review (here: a PhysLean pull request). This specifies the
*process* that produces a submission packet — what a completed submission must contain
and satisfy — as a set of numbered, traceable requirements.

It is distinct from [`verification-method.md`](../../process/verification-method.md),
which is the *how-to* for the four checks. This SRS is the *what must be true*.

- Requirement IDs: `FR-SUB-nnn` (functional), `NFR-SUB-nnn` (non-functional).
- Each requirement is traced to its evidence in [`traceability.md`](traceability.md).
- The requirements are checked by [`check-srs.sh`](check-srs.sh); results in
  [`srs-results.txt`](srs-results.txt).

## 1. Purpose and scope

The process takes a completed piece of formal mathematics (a Lean proof that closes an
open problem) and produces a **reviewer packet** such that an external reviewer can
understand and verify the contribution with the least possible effort, and such that the
contribution conforms to the target project's contribution and AI policies.

In scope: assembling the packet, self-checking it, and staging it for a human to submit.
Out of scope: performing the mathematics; contacting reviewers (done by a human).

## 2. Functional requirements

### FR-SUB-001 — Statement integrity
The submission SHALL prove the target statement **unchanged**. After removing the proof
body and attributes, the formal statement must match the stub/open-problem it closes —
no hypothesis or conclusion altered; only the proof is new.

### FR-SUB-002 — Kernel-level soundness
The submission SHALL carry evidence that the proof depends on **no** `sorry`/`sorryAx`
anywhere in its dependency chain, via `#print axioms`.

### FR-SUB-003 — Reproducibility by one command
The packet SHALL include a single script that reproduces every mandatory check and
exits non-zero if any fails.

### FR-SUB-004 — Human-readable proof
The packet SHALL include a conventional-mathematics rendering of the proof, in exact
step-for-step correspondence with the formal proof, sufficient for a reviewer to judge
mathematical correctness without reading the formal source.

### FR-SUB-005 — Fidelity evidence
The packet SHALL include a check that the human-readable proof faithfully tracks the
formal proof (every load-bearing formal step is present in the writeup), with results.

### FR-SUB-006 — Literature location
The packet SHALL locate the result and its proof route against the published
literature, honestly distinguishing the route used from the classical route.

### FR-SUB-007 — Requirement traceability to the target's guidelines
The submission SHALL trace each of the target project's review guidelines to the
specific evidence that it is met, and SHALL **disclose** (not hide) any guideline only
partially met.

### FR-SUB-008 — Build environment of record
The packet SHALL record the toolchain, dependency revisions, and host used to build the
proof, plus evidence (a build artifact or a fresh transcript) of a successful compile.

### FR-SUB-009 — Reviewer-oriented PR description
The packet SHALL include a pull-request description written for a reviewer seeing the
work cold: what it does, where it goes, the reading order, and the checks.

### FR-SUB-010 — Policy conformance
The submission SHALL conform to the target project's contribution and AI policies:
AI-assisted work is disclosed and personally vouched for by the human author, and
reviewer contact is performed only by the human.

## 3. Non-functional requirements

### NFR-SUB-001 — Ten-minute review
The packet SHOULD be navigable such that a competent reviewer can complete a first-pass
review in under ten minutes.

### NFR-SUB-002 — Evidence honesty
No artifact SHALL present un-evidenced or self-reported work as independently verified.
Self-reported checks (e.g. citation spot-checks) SHALL be labelled as such and kept
distinct from kernel-verified facts.

### NFR-SUB-003 — Staging separation
Preparation artifacts SHALL be clearly separated from an actual submission; the staging
area SHALL state that it is not a submission channel.

### NFR-SUB-004 — Self-containment
The packet SHALL be self-contained: every claim links to an artifact present in the
packet (or an explicitly external, resolvable reference).

## 4. Acceptance

The process is satisfied for a given submission when every `FR-SUB-*` is met with traced
evidence and every `NFR-SUB-*` holds, as recorded in [`traceability.md`](traceability.md)
and confirmed by [`check-srs.sh`](check-srs.sh). A requirement whose evidence is pending
(e.g. a fresh build transcript awaiting a Lean-equipped machine) is marked **partial**,
never silently passed.
