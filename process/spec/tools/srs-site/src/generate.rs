//! Render a validated contribution-spec to a Quarto website (`.qmd` sources).
//!
//! Output layout under `out_dir`:
//! ```text
//!   _quarto.yml          website project + navbar
//!   index.qmd            overview: counts, category index, master table
//!   categories/<c>.qmd   one page per category, each requirement in full
//!   mathlib.qmd          requirements applying to Mathlib, grouped by category
//!   physlean.qmd         requirements applying to PhysLean, grouped by category
//!   traceability.qmd     id -> source -> verify table
//! ```

use crate::model::*;
use std::io;
use std::path::{Path, PathBuf};

/// Canonical category order for navigation and rendering.
pub const CATEGORY_ORDER: &[&str] = &[
    "scope",
    "ai",
    "licensing",
    "naming",
    "style",
    "documentation",
    "commit",
    "pull_request",
    "review",
    "community",
];

fn category_title(cat: &str) -> &str {
    match cat {
        "scope" => "Scope & Remit",
        "ai" => "AI / LLM Policy",
        "licensing" => "Licensing & Copyright",
        "naming" => "Naming Conventions",
        "style" => "Code Style",
        "documentation" => "Documentation",
        "commit" => "Commit Conventions",
        "pull_request" => "Pull-Request Workflow",
        "review" => "Review Process",
        "community" => "Community",
        other => other,
    }
}

fn level_display(l: &str) -> &str {
    match l {
        "shall" => "SHALL",
        "shall_not" => "SHALL NOT",
        "should" => "SHOULD",
        "should_not" => "SHOULD NOT",
        "may" => "MAY",
        "info" => "INFO",
        other => other,
    }
}

fn project_display(p: &str) -> &str {
    match p {
        "mathlib" => "Mathlib",
        "physlean" => "PhysLean",
        "both" => "Mathlib + PhysLean",
        other => other,
    }
}

fn cat_rank(cat: &str) -> usize {
    CATEGORY_ORDER.iter().position(|c| *c == cat).unwrap_or(usize::MAX)
}

/// Requirements in stable render order: by canonical category, then by id.
fn ordered(reqs: &[Requirement]) -> Vec<&Requirement> {
    let mut v: Vec<&Requirement> = reqs.iter().collect();
    v.sort_by(|a, b| {
        cat_rank(a.word("category").unwrap_or(""))
            .cmp(&cat_rank(b.word("category").unwrap_or("")))
            .then_with(|| a.id.cmp(&b.id))
    });
    v
}

fn applies(r: &Requirement, project: &str) -> bool {
    matches!(r.word("project"), Some("both")) || r.word("project") == Some(project)
}

/// Render one requirement as a markdown section (used by category & project pages).
fn render_req(out: &mut String, r: &Requirement) {
    let id = &r.id;
    let anchor = id.to_lowercase();
    let title = r.text("title").unwrap_or("(untitled)");
    out.push_str(&format!("### {id} — {title} {{#sec-{anchor}}}\n\n"));
    out.push_str(&format!(
        "**{}** · Level **{}**\n\n",
        project_display(r.word("project").unwrap_or("")),
        level_display(r.word("level").unwrap_or("")),
    ));
    out.push_str(r.text("statement").unwrap_or(""));
    out.push_str("\n\n");

    if let Some(items) = r.list("acceptance") {
        out.push_str("**Acceptance criteria**\n\n");
        for it in items {
            out.push_str(&format!("- {it}\n"));
        }
        out.push('\n');
    }
    if let Some(rat) = r.text("rationale") {
        out.push_str(&format!("**Rationale.** {rat}\n\n"));
    }
    if let Some(v) = r.text("verify") {
        out.push_str(&format!("**Verify.** {v}\n\n"));
    }
    out.push_str(&format!("**Source.** <{}>\n\n", r.text("source").unwrap_or("")));
    out.push_str("---\n\n");
}

/// Generate the whole site; returns the list of files written.
pub fn generate(spec: &Spec, out_dir: &Path) -> io::Result<Vec<String>> {
    let mut written = Vec::new();
    std::fs::create_dir_all(out_dir)?;
    let cats_dir = out_dir.join("categories");
    std::fs::create_dir_all(&cats_dir)?;

    // categories actually present, in canonical order
    let present: Vec<&str> = CATEGORY_ORDER
        .iter()
        .copied()
        .filter(|c| spec.requirements.iter().any(|r| r.word("category") == Some(*c)))
        .collect();

    write_file(out_dir.join("_quarto.yml"), &render_quarto_yml(&present), &mut written)?;
    write_file(out_dir.join("index.qmd"), &render_index(spec, &present), &mut written)?;
    for c in &present {
        write_file(cats_dir.join(format!("{c}.qmd")), &render_category_page(spec, c), &mut written)?;
    }
    write_file(out_dir.join("mathlib.qmd"), &render_project_page(spec, "mathlib", &present), &mut written)?;
    write_file(out_dir.join("physlean.qmd"), &render_project_page(spec, "physlean", &present), &mut written)?;
    write_file(out_dir.join("traceability.qmd"), &render_traceability(spec), &mut written)?;
    Ok(written)
}

fn write_file(path: PathBuf, content: &str, written: &mut Vec<String>) -> io::Result<()> {
    std::fs::write(&path, content)?;
    written.push(path.display().to_string());
    Ok(())
}

fn render_quarto_yml(present: &[&str]) -> String {
    let mut y = String::new();
    y.push_str("project:\n  type: website\n  output-dir: _site\n\n");
    y.push_str("website:\n");
    y.push_str("  title: \"Lean Contribution SRS\"\n");
    y.push_str("  description: \"Mathlib & PhysLean contribution guidelines as a governed requirements catalogue\"\n");
    y.push_str("  navbar:\n    left:\n");
    y.push_str("      - href: index.qmd\n        text: Overview\n");
    y.push_str("      - text: Categories\n        menu:\n");
    for c in present {
        y.push_str(&format!("          - href: categories/{c}.qmd\n            text: \"{}\"\n", category_title(c)));
    }
    y.push_str("      - href: mathlib.qmd\n        text: Mathlib\n");
    y.push_str("      - href: physlean.qmd\n        text: PhysLean\n");
    y.push_str("      - href: traceability.qmd\n        text: Traceability\n");
    y.push_str("    right:\n      - icon: github\n        href: https://github.com/leanprover-community/mathlib4\n\n");
    y.push_str("format:\n  html:\n    theme: cosmo\n    toc: true\n    toc-depth: 3\n    number-sections: false\n");
    y
}

fn count_where(spec: &Spec, pred: impl Fn(&Requirement) -> bool) -> usize {
    spec.requirements.iter().filter(|r| pred(r)).count()
}

fn render_index(spec: &Spec, present: &[&str]) -> String {
    let mut s = String::new();
    s.push_str("---\ntitle: \"Mathlib & PhysLean Contribution SRS\"\n---\n\n");
    if let Some(m) = &spec.system.mission {
        s.push_str(&format!("> {m}\n\n"));
    }
    s.push_str("Generated from a Varro requirements specification: every guideline for contributing to ");
    s.push_str("[Mathlib](https://github.com/leanprover-community/mathlib4) and ");
    s.push_str("[PhysLean / Physlib](https://github.com/leanprover-community/physlib) is a uniquely-identified, typed requirement. ");
    s.push_str("**Do not edit these pages by hand** — edit the `varro/*.varro` sources and re-run `srs-site generate`.\n\n");

    let total = spec.requirements.len();
    let ml = count_where(spec, |r| applies(r, "mathlib"));
    let pl = count_where(spec, |r| applies(r, "physlean"));
    s.push_str(&format!("**{total} requirements** — {ml} apply to Mathlib, {pl} to PhysLean.\n\n"));

    s.push_str("## Obligation levels\n\n| Level | Count |\n|---|---:|\n");
    for lvl in ["shall", "shall_not", "should", "should_not", "may", "info"] {
        let n = count_where(spec, |r| r.word("level") == Some(lvl));
        if n > 0 {
            s.push_str(&format!("| {} | {n} |\n", level_display(lvl)));
        }
    }
    s.push('\n');

    s.push_str("## Categories\n\n| Category | Count | |\n|---|---:|---|\n");
    for c in present {
        let n = count_where(spec, |r| r.word("category") == Some(*c));
        s.push_str(&format!("| {} | {n} | [browse](categories/{c}.qmd) |\n", category_title(c)));
    }
    s.push('\n');

    s.push_str("## All requirements\n\n| ID | Requirement | Applies to | Level |\n|---|---|---|---|\n");
    for r in ordered(&spec.requirements) {
        let id = &r.id;
        let cat = r.word("category").unwrap_or("");
        let anchor = id.to_lowercase();
        s.push_str(&format!(
            "| [{id}](categories/{cat}.qmd#sec-{anchor}) | {} | {} | {} |\n",
            r.text("title").unwrap_or(""),
            project_display(r.word("project").unwrap_or("")),
            level_display(r.word("level").unwrap_or("")),
        ));
    }
    s.push('\n');
    s
}

fn render_category_page(spec: &Spec, cat: &str) -> String {
    let mut s = String::new();
    s.push_str(&format!("---\ntitle: \"{}\"\n---\n\n", category_title(cat)));
    let reqs: Vec<&Requirement> = ordered(&spec.requirements)
        .into_iter()
        .filter(|r| r.word("category") == Some(cat))
        .collect();
    s.push_str(&format!("{} requirement(s) in this category.\n\n", reqs.len()));
    for r in reqs {
        render_req(&mut s, r);
    }
    s
}

fn render_project_page(spec: &Spec, project: &str, present: &[&str]) -> String {
    let mut s = String::new();
    s.push_str(&format!("---\ntitle: \"{} Requirements\"\n---\n\n", project_display(project)));
    s.push_str(&format!(
        "Every requirement that applies to {}. Items marked *Mathlib + PhysLean* apply to both projects.\n\n",
        project_display(project)
    ));
    for c in present {
        let reqs: Vec<&Requirement> = ordered(&spec.requirements)
            .into_iter()
            .filter(|r| r.word("category") == Some(*c) && applies(r, project))
            .collect();
        if reqs.is_empty() {
            continue;
        }
        s.push_str(&format!("## {}\n\n", category_title(c)));
        for r in reqs {
            render_req(&mut s, r);
        }
    }
    s
}

fn render_traceability(spec: &Spec) -> String {
    let mut s = String::new();
    s.push_str("---\ntitle: \"Traceability\"\n---\n\n");
    s.push_str("Each requirement traced to the upstream source it derives from and the check that verifies conformance.\n\n");
    s.push_str("| ID | Applies to | Level | Source | Verify |\n|---|---|---|---|---|\n");
    for r in ordered(&spec.requirements) {
        let id = &r.id;
        let verify = r.text("verify").unwrap_or("—").replace('|', "\\|");
        s.push_str(&format!(
            "| {id} | {} | {} | [source]({}) | {verify} |\n",
            project_display(r.word("project").unwrap_or("")),
            level_display(r.word("level").unwrap_or("")),
            r.text("source").unwrap_or(""),
        ));
    }
    s.push('\n');
    s
}
