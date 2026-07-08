# Plan — kernel-verified Lean refactoring, and where it leads

**Anchor:** land the PR2 sandwiched-Rényi split for JTS in a **completely-proved, near-risk-free**
way — using Lean metaprogramming, not text parsing — and in doing so build the reusable
substrate for signature-based discovery of common mathematics across the corpus.

**Strategic frame (why this shape).** Philip is not, and need not become, a Lean expert. The
edge is systems + tooling, not mathematics. Kernel-verified tooling *enforces* the rigour that
can't be personally eyeballed — the faithfulness check makes shipping an unfaithful refactor
mechanically impossible, independent of maths depth. So the play is to route around the maths
via meta-tooling (home territory) and let the kernel be the guarantor. Milestone 1 is
deliberately small; later milestones are sequenced strictly behind it and must not inflate it.

---

## What is PROVEN vs INFERRED (honesty ledger — the plan respects this line)

| Capability | Status | Evidence |
|---|---|---|
| Extract the exact dependency DAG from the compiled env | **PROVEN** | `Expr.getUsedConstants`; ~100ms for 5k constants / 148k edges |
| Exact file membership per constant | **PROVEN** | `getModuleIdxFor?` + `header.moduleNames` |
| Kernel signature per constant (the "distance signature") | **PROVEN** | `ConstantInfo.type`; already dumped, hygiene-normalizable |
| Source span per constant (source-linking) | **PROVEN** | `findDeclarationRanges?` → line spans |
| Faithfulness = "after-DAG ≡ before-DAG modulo module + a reviewed delta-whitelist" | **SOUND, unbuilt** | the check is a diff over proven data; not yet coded as one tool |
| Proof-search acceleration (defeq / unify / typecheck-candidate queries) | **INFERRED** | `MetaM` exposes it; NOT prototyped — do not depend on it in M1 |

**The one caveat that governs everything:** the DAG check proves *what changed* with kernel
precision; it does **not** decide *whether a change was intended*. Privacy promotions, aliases,
a def split to break a cycle — all legitimate — make the DAGs legitimately differ. So the tool
outputs "identical except for THIS explicit whitelist"; a human/AI still adjudicates the
whitelist (e.g. PR2's two open design decisions). Precision on detection; judgment on intent.
Never let "mathematically precise" slide into "no judgment required" — that conflation is
exactly the "merely true" failure JTS rejects.

---

## Feature set (the full vision, so milestones have a horizon)

1. **Quantified refactoring** — propose a constant→file partition; verify acyclicity; prove
   faithfulness against the kernel; emit the move. (M1)
2. **Kernel-verified faithfulness reporting** — the before/after DAG diff as PR evidence, so a
   reviewer trusts a large move without re-reading it. (M1)
3. **Structure visualization** — the sunburst / graph, fed by the *real* extracted DAG (not the
   regex approximation shipped today). (M2)
4. **Signature-based discovery** — "find lemmas whose type is structurally near this one" across
   the corpus; the unification-of-common-maths frontier. (M3 — the harder, further goal)
5. **Proof-development support** — warm-process `MetaM` queries (what unifies here, is this
   defeq, does this candidate typecheck). (M4 — inferred; de-risk before committing)
6. **Varro integration** — the above as verbs behind a `LeanResolved` resolver, trust-tiered
   (`Fact`/`Constraint`/`Suggestion`) with source-refs, unified with the platform. (cross-cutting,
   phased in once M1–M3 have proven the resolver payloads)

---

## Local vs remote AI (interaction model)

The Lean environment load (~20s of `import`) is the only real cost; introspection after is ~100ms.
This shapes who runs what:

- **Remote AI (Codex, on the Helios build schedule):** executes the *batch* operations — run the
  extractor, run the faithfulness check, perform the gated move, regenerate evidence. These are
  one-shot: load env, extract, emit, done. No interactivity needed; latency irrelevant. **M1–M2
  are remote-AI shaped.**
- **Local AI (interactive proof work):** benefits from a **warm, long-lived Lean process** so the
  ~20s load is paid once and successive `MetaM` queries are ~ms. This is the M4 proof-support
  tier and the only part that *needs* persistence. It does **not** need to be as instant as awk/grep
  — Philip's own read — so a modest local query loop suffices; full interactivity is not a M1 gate.
- **Boundary:** both consume the *same* extracted JSON / query protocol. Lean stays Lean (the
  authoritative side); Rust/Varro/the AI consume serialized structured facts. Tier-3 in-process FFI
  is explicitly rejected — its only advantage (zero-copy handles) is wasted on an AI/serialized
  consumer.

---

## Milestone 1 — the tight first tool (lands PR2 for JTS)

**Goal:** one command that takes a target partition and lands it, kernel-proved.

Deliverables (all Lean-metaprogram-based; NO awk/grep in the trust path):
- **M1.a `extract-dag`** — metaprogram: for a module-set, emit JSON
  `{ name, module, source_span, signature_hash, in_set_deps[] }` per constant. (Extends the probes
  already proven; the source-span + signature fields are proven available.)
- **M1.b `check-partition`** — given a proposed constant→file assignment: verify the file-level
  graph is **acyclic** (reject if not, naming the offending edge), and confirm every declaration is
  assigned. Pure graph check over M1.a output.
- **M1.c `verify-faithful`** — given `before` (current Relative.lean) and `after` (the moved files),
  both compiled: assert the induced DAG + signatures are identical **modulo module + the reviewed
  delta-whitelist**. Emit a report: "N constants moved, 0 unexpected edge/type changes, whitelist
  = {10 privacy promotions, 1 alias}." This is the risk-elimination: it is a kernel-level theorem
  about the artifacts, not a text hash.
- **M1.d execution** — the gated move itself (still per-phase `lake build`), but the *evidence* is
  now M1.c's report, not the text harness. The text harness (H1/H2/H4) is **retired** — subsumed.

**Definition of done for M1:** PR2's 7-file (or the reviewed final) partition executed; `verify-faithful`
green; the report is the PR body's evidence; the two open design decisions (D-OPEN-1/2) resolved by
Philip. Blocked on: #1378 merge (stable base) + the resolution of D-OPEN-1/2.

**Explicitly OUT of M1:** visualization polish, Varro integration, signature *search*, proof support.
M1 produces the signature *data* (free), but querying it is M3.

---

## Milestones 2–4 (sequenced behind M1; each consumes M1's output)

- **M2 — real-data visualization.** Replace today's regex-based sunburst with one fed by
  `extract-dag`. Small; mostly re-pointing the viewer at true data. Remote-AI buildable.
- **M3 — signature discovery.** Over the whole corpus's `extract-dag` output, structural
  type-similarity search ("what's near this lemma"). This is the unification-of-common-maths goal.
  **Frontier warning:** signatures yield *candidates*; deciding two theorems are genuinely the same
  may need defeq (kernel) and sometimes mathematical judgment — the tool surfaces, a
  mathematician/JTS adjudicates. Do not assume signatures alone close it.
- **M4 — proof support.** Warm-process `MetaM` query loop. **Gate:** prototype ONE query
  (e.g. "lemmas unifying with this goal") before scheduling the rest — this is the sole inferred
  capability and must be de-risked before it anchors work.

---

## Helios build schedule (for Codex execution)

Sequenced, each step independently verifiable. Steps 1–4 are M1 and can start once #1378 merges.

| # | Step | Produces | Gate | Depends on |
|---|---|---|---|---|
| 1 | Build `extract-dag` metaprogram + JSON schema | ground-truth graph substrate | runs, emits valid JSON for QuantumInfo | proven APIs |
| 2 | Re-derive the Relative.lean partition design from `extract-dag` (replace regex) | corrected clusters + true edges + acyclicity | design DAG proven acyclic (resolves the 2 open decisions with real data) | 1 |
| 3 | Build `check-partition` + `verify-faithful` | the faithfulness theorem-checker | no-op self-validates (before≡before); catches an injected fake change | 1 |
| 4 | Execute PR2 move, gated; emit `verify-faithful` report | the PR + its kernel evidence | verify-faithful green; full `lake build`; lint | 2,3, #1378 merged, D-OPEN-1/2 resolved |
| 5 | Point the sunburst/viewer at `extract-dag` output (M2) | real-data visualization | renders from true data | 1 |
| 6 | Corpus-wide `extract-dag` + signature index (M3 groundwork) | the discovery substrate | index builds; a hand-checked "related" pair scores high | 1 |
| 7 | Prototype ONE proof-search query (M4 gate) | go/no-go on proof support | the query returns correct candidates on a known goal | warm-process link |

**Codex guardrails:** steps 1–3 touch NO physlib source (they read the compiled env / build tools
in the submissions or a tools repo). Step 4 is the only one that edits physlib, gated per phase,
and never pushes/opens the PR (Philip's action, per AI-POLICY §3.1). Step 7 must not be scheduled
downstream-of until it returns green — it is the one unproven link.

---

## Bottom line

Milestone 1 is small, its core mechanics are proven today, and it lands PR2 for JTS with a
kernel-level faithfulness guarantee — turning a nerve-wracking 1450-line manual move into a
checked, near-risk-free operation. It also emits, for free, the signature data that seeds the
larger unification goal. Build the small thing; let it earn the rest. The only capability the plan
does not yet stand on — proof-search acceleration — is fenced behind an explicit prototype gate so
the schedule never assumes what hasn't been shown.
