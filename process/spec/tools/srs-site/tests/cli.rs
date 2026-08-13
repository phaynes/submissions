//! Integration tests: the real spec must validate, and each fail-closed rule must fire.

use srs_site::{load_dir, parser, validate};
use std::path::{Path, PathBuf};

fn manifest(rel: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(rel)
}

/// A minimal valid system header, so requirement-level tests have a schema to check.
fn header() -> &'static str {
    r#"
    system test.spec {
      mission "t"
      authority lane "operator:test"
      domain formal-mathematics
      maturity checked
      enum Level { shall, shall_not, should, should_not, may, info }
      enum Project { mathlib, physlean, both }
      enum Category { scope, ai, licensing, naming, style, documentation, commit, pull_request, review, community }
      type Requirement {
        field id: ident required
        field title: string required
        field project: Project required
        field category: Category required
        field level: Level required
        field source: uri required
        field statement: markdown required
        field rationale: markdown optional
        field acceptance: list required
        field verify: string optional
      }
    }
    "#
}

fn with(req: &str) -> validate::Report {
    let src = format!("{}{req}", header());
    let spec = parser::parse(&src).expect("parse");
    validate::validate(&spec)
}

#[test]
fn real_spec_is_valid() {
    let spec = load_dir(&manifest("../../varro")).expect("load real spec");
    let report = validate::validate(&spec);
    assert!(report.ok(), "expected a clean spec, got errors:\n{:#?}", report.errors);
    assert!(report.counts.total >= 40, "expected many requirements, got {}", report.counts.total);
    assert!(report.counts.by_category.contains_key("style"));
    assert!(report.counts.mathlib > 0 && report.counts.physlean > 0);
}

#[test]
fn parses_unicode_and_escapes() {
    let src = r#"
      requirement STY-999 {
        title "unicode ↦ ∈ ≤ then newline\nsecond line"
        project both
        category style
        level shall
        source "https://example.com"
        statement "α β γ ∑ ∏"
        acceptance [ "one", "two" ]
      }
    "#;
    let spec = parser::parse(src).expect("parse");
    let r = &spec.requirements[0];
    assert!(r.text("title").unwrap().contains('\n'));
    assert!(r.text("statement").unwrap().contains('α'));
    assert_eq!(r.list("acceptance").unwrap().len(), 2);
}

#[test]
fn rejects_duplicate_id() {
    let report = with(
        r#"
        requirement STY-001 { title "a" project both category style level shall source "https://x.io" statement "s" acceptance ["x"] }
        requirement STY-001 { title "b" project both category style level shall source "https://x.io" statement "s" acceptance ["x"] }
    "#,
    );
    assert!(report.errors.iter().any(|e| e.contains("duplicate id")), "{:#?}", report.errors);
}

#[test]
fn rejects_unknown_level() {
    let report = with(
        r#"requirement STY-002 { title "a" project both category style level frequently source "https://x.io" statement "s" acceptance ["x"] }"#,
    );
    assert!(report.errors.iter().any(|e| e.contains("not a valid Level")), "{:#?}", report.errors);
}

#[test]
fn rejects_prefix_category_mismatch() {
    let report = with(
        r#"requirement STY-003 { title "a" project both category naming level shall source "https://x.io" statement "s" acceptance ["x"] }"#,
    );
    assert!(report.errors.iter().any(|e| e.contains("disagrees with id prefix")), "{:#?}", report.errors);
}

#[test]
fn rejects_non_url_source() {
    let report = with(
        r#"requirement STY-004 { title "a" project both category style level shall source "ftp://x" statement "s" acceptance ["x"] }"#,
    );
    assert!(report.errors.iter().any(|e| e.contains("must be an http")), "{:#?}", report.errors);
}

#[test]
fn rejects_missing_required_field() {
    // no `statement`
    let report = with(
        r#"requirement STY-005 { title "a" project both category style level shall source "https://x.io" acceptance ["x"] }"#,
    );
    assert!(report.errors.iter().any(|e| e.contains("missing required field `statement`")), "{:#?}", report.errors);
}

#[test]
fn rejects_unknown_field() {
    let report = with(
        r#"requirement STY-006 { title "a" project both category style level shall source "https://x.io" statement "s" acceptance ["x"] surprise "boo" }"#,
    );
    assert!(report.errors.iter().any(|e| e.contains("unknown field `surprise`")), "{:#?}", report.errors);
}

#[test]
fn rejects_bad_id_format() {
    let report = with(
        r#"requirement STY1 { title "a" project both category style level shall source "https://x.io" statement "s" acceptance ["x"] }"#,
    );
    assert!(report.errors.iter().any(|e| e.contains("does not match")), "{:#?}", report.errors);
}
