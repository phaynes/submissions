# Contribution SRS — Mathlib & PhysLean

A **formal software/process requirements specification** of what it takes to contribute
and produce code for [Mathlib](https://github.com/leanprover-community/mathlib4) and
[PhysLean / Physlib](https://github.com/leanprover-community/physlib). Every upstream
guideline — scope, AI policy, licensing, naming, style, documentation, commits,
pull-request workflow, review, community — is captured as a **uniquely-identified,
typed requirement** in a Varro specification, and a small Rust tool validates that
specification (fail-closed) and renders it to a Quarto website.

This follows the Helios SRS convention (`FR/NFR`-style requirements, SHALL/SHOULD
language, traceability to evidence) and the way Helios uses VSL: a `system` header with
`enum`/`type` declarations. It adds one construct — a first-class `requirement` block —
so the guidelines *live in Varro* rather than in prose.

## Layout

```
spec/
├── varro/                  ← the SRS itself (authoritative source, hand-edited)
│   ├── 00-system.varro     ← system header: mission, closed enums, `type Requirement`
│   ├── 10-scope.varro      ← one file per category of requirements
│   ├── 20-ai-policy.varro
│   ├── 30-licensing.varro
│   ├── 40-naming.varro
│   ├── 50-style.varro
│   ├── 60-documentation.varro
│   ├── 70-commit.varro
│   ├── 80-pull-request.varro
│   ├── 90-review.varro
│   └── 95-community.varro
├── tools/srs-site/         ← Rust: parse → validate (fail-closed) → generate .qmd
│   ├── src/{model,parser,validate,generate}.rs, lib.rs, main.rs
│   └── tests/cli.rs
└── site/                   ← GENERATED Quarto site (do not hand-edit)
    ├── _quarto.yml, index.qmd, categories/*.qmd, mathlib.qmd, physlean.qmd, traceability.qmd
    └── _site/              ← rendered HTML (git-ignored)
```

## The Varro requirements DSL

The DSL reuses VSL's vocabulary (`system`, `mission`, `authority lane`, `domain`,
`maturity`, `enum`, `type … { field … }`) and adds `requirement <ID> { … }` blocks.
Each requirement is validated against the `type Requirement` schema and the closed
enums declared in `00-system.varro`.

```varro
requirement STY-001 {
  title "100-character line limit"
  project both                 // Project enum: mathlib | physlean | both
  category style               // Category enum; MUST match the id prefix
  level shall                  // Level enum: shall | shall_not | should | should_not | may | info
  source "https://leanprover-community.github.io/contribute/style.html"
  statement "Lines SHALL NOT be longer than 100 characters."
  rationale "Short lines stay readable on small screens and in side-by-side diffs."
  acceptance [ "No source line exceeds 100 characters.",
               "The style linter reports no line-length violations." ]
  verify "lake exe lint-style"
}
```

### Requirement ID grammar

`<PREFIX>-<NNN>` (zero-padded 3 digits). The prefix is bound one-to-one to a category,
and a requirement whose `category` field disagrees with its id prefix is a **hard
error**:

| Prefix | Category | Prefix | Category |
|---|---|---|---|
| `SCOPE` | scope | `DOC` | documentation |
| `AI` | ai | `CMT` | commit |
| `LIC` | licensing | `PR` | pull_request |
| `NAM` | naming | `RVW` | review |
| `STY` | style | `COM` | community |

## Usage

Run from this `spec/` directory (defaults are `--spec varro`, `--out site`):

```bash
# validate the spec (fail-closed) — prints counts, warnings, PASS/FAIL
cargo run --manifest-path tools/srs-site/Cargo.toml -- check

# validate, then (re)generate the Quarto .qmd site
cargo run --manifest-path tools/srs-site/Cargo.toml -- generate

# render the site to HTML
( cd site && quarto render )        # → site/_site/index.html

# run the test suite (parser + every fail-closed rule)
cargo test --manifest-path tools/srs-site/Cargo.toml
```

**Exit codes** (the fail-closed taxonomy): `0` pass · `1` spec invalid (content) ·
`3` environment/usage error. Missing or unreadable input is `3` and never a false green;
`generate` refuses to run on an invalid spec.

## Adding or changing a requirement

1. Edit the relevant `varro/NN-*.varro` file (or add a new `requirement` block).
2. `… -- check` until it is `PASS` (the validator enforces unique IDs, the ID↔category
   binding, closed-vocabulary values, required fields, and http(s) sources).
3. `… -- generate`, then `( cd site && quarto render )`.

Never hand-edit `site/*.qmd` — they are regenerated from `varro/` and will be overwritten.

## Validation guarantees

`srs-site check` fails closed on: a duplicate ID; an ID that does not match the grammar;
a `category` that disagrees with the ID prefix; a value outside a closed enum
(`level`/`project`/`category`); a missing required field; a non-`http(s)` `source`; a
field not declared in `type Requirement`; a missing `system`/`enum`/`type Requirement`.
It additionally reports **non-blocking warnings** for normative requirements that carry
no `verify` (i.e. rules with no stated automated check) — a coverage signal, tunable in
`tools/srs-site/src/validate.rs::quality_warnings`.
