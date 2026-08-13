//! Fail-closed validation of a parsed contribution-spec.
//!
//! Two channels:
//!   * **errors**  — block generation (exit 1). Structural / schema / integrity faults.
//!   * **warnings** — reported but non-blocking. House quality heuristics you can tune
//!                    in [`quality_warnings`].
//!
//! Exit-code taxonomy (applied by the binary): `0` pass · `1` content invalid ·
//! `3` environment/IO. Missing or unreadable input is `3` and never a false green.

use crate::model::*;
use std::collections::{BTreeMap, BTreeSet};

/// Canonical binding of an ID prefix to its `Category` value. A requirement whose id
/// prefix is absent here, or whose `category` field disagrees with the bound value, is
/// rejected. This is the single source of truth for the `<PREFIX>-<NNN>` grammar.
pub const PREFIX_CATEGORY: &[(&str, &str)] = &[
    ("SCOPE", "scope"),
    ("AI", "ai"),
    ("LIC", "licensing"),
    ("NAM", "naming"),
    ("STY", "style"),
    ("DOC", "documentation"),
    ("CMT", "commit"),
    ("PR", "pull_request"),
    ("RVW", "review"),
    ("COM", "community"),
];

#[derive(Default)]
pub struct Counts {
    pub total: usize,
    pub by_level: BTreeMap<String, usize>,
    pub by_category: BTreeMap<String, usize>,
    pub mathlib: usize,
    pub physlean: usize,
}

pub struct Report {
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
    pub counts: Counts,
}

impl Report {
    pub fn ok(&self) -> bool {
        self.errors.is_empty()
    }
}

/// Is `id` of the form `<PREFIX>-<NNN>` — uppercase letters, a dash, exactly 3 digits?
fn valid_id(id: &str) -> bool {
    match id.split_once('-') {
        Some((prefix, num)) => {
            !prefix.is_empty()
                && prefix.chars().all(|c| c.is_ascii_uppercase())
                && num.len() == 3
                && num.chars().all(|c| c.is_ascii_digit())
        }
        None => false,
    }
}

fn prefix_of(id: &str) -> &str {
    id.split_once('-').map(|(p, _)| p).unwrap_or("")
}

/// Validate a whole spec against its own declared schema and the ID grammar.
pub fn validate(spec: &Spec) -> Report {
    let mut errors = Vec::new();
    let sys = &spec.system;

    // ---- structural: required closed vocabularies + the Requirement schema --------
    for needed in ["Level", "Project", "Category"] {
        if !sys.enums.contains_key(needed) {
            errors.push(format!("system is missing `enum {needed}`"));
        }
    }
    let schema = match sys.types.get("Requirement") {
        Some(t) => t,
        None => {
            errors.push("system is missing `type Requirement`".into());
            return Report { errors, warnings: Vec::new(), counts: Counts::default() };
        }
    };
    let schema_names: BTreeSet<&str> = schema.fields.iter().map(|f| f.name.as_str()).collect();
    let prefix_map: BTreeMap<&str, &str> = PREFIX_CATEGORY.iter().copied().collect();

    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut counts = Counts::default();

    for r in &spec.requirements {
        let at = format!("{} (line {})", r.id, r.line);

        // id format + uniqueness
        if !valid_id(&r.id) {
            errors.push(format!("{at}: id `{}` does not match <PREFIX>-<NNN>", r.id));
        }
        if !seen.insert(r.id.as_str()) {
            errors.push(format!("{at}: duplicate id `{}`", r.id));
        }

        // id prefix <-> category binding
        let prefix = prefix_of(&r.id);
        match (prefix_map.get(prefix).copied(), r.word("category")) {
            (None, _) => errors.push(format!("{at}: id prefix `{prefix}` is not a known category prefix")),
            (Some(bound), Some(decl)) if bound != decl => {
                errors.push(format!("{at}: category `{decl}` disagrees with id prefix `{prefix}` (=> `{bound}`)"));
            }
            _ => {}
        }

        // every schema field (id is satisfied by the header, so skip it)
        for fd in &schema.fields {
            if fd.name == "id" {
                continue;
            }
            match r.fields.get(&fd.name) {
                None => {
                    if fd.required {
                        errors.push(format!("{at}: missing required field `{}`", fd.name));
                    }
                }
                Some(v) => {
                    for e in check_value(&fd.name, &fd.type_ref, v, &sys.enums) {
                        errors.push(format!("{at}: {e}"));
                    }
                }
            }
        }

        // no fields outside the schema
        for k in r.fields.keys() {
            if !schema_names.contains(k.as_str()) {
                errors.push(format!("{at}: unknown field `{k}` (not in `type Requirement`)"));
            }
        }

        // counts
        counts.total += 1;
        if let Some(l) = r.word("level") {
            *counts.by_level.entry(l.to_string()).or_default() += 1;
        }
        if let Some(c) = r.word("category") {
            *counts.by_category.entry(c.to_string()).or_default() += 1;
        }
        match r.word("project") {
            Some("mathlib") => counts.mathlib += 1,
            Some("physlean") => counts.physlean += 1,
            Some("both") => {
                counts.mathlib += 1;
                counts.physlean += 1;
            }
            _ => {}
        }
    }

    let warnings = quality_warnings(spec);
    Report { errors, warnings, counts }
}

/// Check one field value against its declared schema type.
fn check_value(fname: &str, type_ref: &str, v: &Value, enums: &BTreeMap<String, Vec<String>>) -> Vec<String> {
    let mut errs = Vec::new();
    let is_enum = enums.contains_key(type_ref);
    match v {
        Value::Text(s) => match type_ref {
            "string" | "markdown" => {
                if s.trim().is_empty() {
                    errs.push(format!("field `{fname}` is empty"));
                }
            }
            "uri" => {
                if !(s.starts_with("http://") || s.starts_with("https://")) {
                    errs.push(format!("field `{fname}` must be an http(s) URL, got `{s}`"));
                }
            }
            _ => errs.push(format!("field `{fname}` expects {type_ref}, got a quoted string")),
        },
        Value::Word(s) => {
            if is_enum {
                if !enums[type_ref].iter().any(|x| x == s) {
                    errs.push(format!("field `{fname}`: `{s}` is not a valid {type_ref} (one of {:?})", enums[type_ref]));
                }
            } else if type_ref == "ident" {
                if s.trim().is_empty() {
                    errs.push(format!("field `{fname}` is empty"));
                }
            } else {
                errs.push(format!("field `{fname}` expects {type_ref}, got bare word `{s}`"));
            }
        }
        Value::List(items) => {
            if type_ref != "list" {
                errs.push(format!("field `{fname}` expects {type_ref}, got a list"));
            } else if items.is_empty() {
                errs.push(format!("field `{fname}` must have at least one item"));
            } else if items.iter().any(|x| x.trim().is_empty()) {
                errs.push(format!("field `{fname}` has an empty list item"));
            }
        }
    }
    errs
}

/// Non-blocking house quality heuristics.
///
/// ─────────────────────────────────────────────────────────────────────────────
/// ★ This is the tuning surface that is genuinely yours. The schema checks above are
///   objective (a field is present or it isn't); these are *policy* — how strict the
///   SRS quality bar should be. The one heuristic below flags normative requirements
///   (SHALL/SHOULD/…) that carry no `verify`, i.e. rules with no stated conformance
///   check. Add your own rules here, or promote a warning to a hard error by pushing
///   into `errors` in `validate` instead. See the note at the end of the session.
/// ─────────────────────────────────────────────────────────────────────────────
pub fn quality_warnings(spec: &Spec) -> Vec<String> {
    let mut warnings = Vec::new();
    let normative = ["shall", "shall_not", "should", "should_not"];
    for r in &spec.requirements {
        let level = r.word("level").unwrap_or("");
        if normative.contains(&level) && r.text("verify").is_none() {
            warnings.push(format!("{}: normative ({level}) but has no `verify` (no automated conformance check)", r.id));
        }
    }
    warnings
}
