//! `srs-site` — parse, validate, and render the Varro contribution-spec.
//!
//! ```text
//!   srs-site check    [--spec <dir>]                 validate only
//!   srs-site generate [--spec <dir>] [--out <dir>]   validate, then emit the Quarto site
//! ```
//! Exit codes: `0` ok · `1` spec invalid · `3` environment / usage error.

use srs_site::{generate, load_dir, model, validate, LoadError};
use std::path::{Path, PathBuf};
use std::process::exit;

fn main() {
    exit(run());
}

fn run() -> i32 {
    let args: Vec<String> = std::env::args().collect();
    let cmd = args.get(1).map(|s| s.as_str()).unwrap_or("help");

    let mut spec_dir = PathBuf::from("varro");
    let mut out_dir = PathBuf::from("site");
    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--spec" => {
                i += 1;
                if let Some(v) = args.get(i) {
                    spec_dir = PathBuf::from(v);
                }
            }
            "--out" => {
                i += 1;
                if let Some(v) = args.get(i) {
                    out_dir = PathBuf::from(v);
                }
            }
            other => {
                eprintln!("error: unknown argument `{other}`");
                return 3;
            }
        }
        i += 1;
    }

    match cmd {
        "check" => do_check(&spec_dir),
        "generate" => do_generate(&spec_dir, &out_dir),
        "help" | "-h" | "--help" => {
            print_help();
            0
        }
        other => {
            eprintln!("error: unknown command `{other}`\n");
            print_help();
            3
        }
    }
}

fn load(spec_dir: &Path) -> Result<model::Spec, i32> {
    load_dir(spec_dir).map_err(|LoadError { code, msg }| {
        eprintln!("error: {msg}");
        code
    })
}

fn do_check(spec_dir: &Path) -> i32 {
    let spec = match load(spec_dir) {
        Ok(s) => s,
        Err(c) => return c,
    };
    let report = validate::validate(&spec);
    print_report(&spec, &report);
    if report.ok() {
        0
    } else {
        1
    }
}

fn do_generate(spec_dir: &Path, out_dir: &Path) -> i32 {
    let spec = match load(spec_dir) {
        Ok(s) => s,
        Err(c) => return c,
    };
    let report = validate::validate(&spec);
    print_report(&spec, &report);
    if !report.ok() {
        eprintln!("refusing to generate from an invalid spec");
        return 1;
    }
    match generate::generate(&spec, out_dir) {
        Ok(written) => {
            println!("\ngenerated {} files under {}:", written.len(), out_dir.display());
            for w in &written {
                println!("  {w}");
            }
            0
        }
        Err(e) => {
            eprintln!("error: failed to write site: {e}");
            3
        }
    }
}

fn print_report(spec: &model::Spec, report: &validate::Report) {
    println!("=== contribution-spec check ===");
    println!(
        "system: {} (maturity: {})",
        spec.system.name,
        spec.system.maturity.as_deref().unwrap_or("?")
    );
    let c = &report.counts;
    println!("requirements: {}   (mathlib: {}, physlean: {})", c.total, c.mathlib, c.physlean);

    let level = c
        .by_level
        .iter()
        .map(|(k, v)| format!("{k} {v}"))
        .collect::<Vec<_>>()
        .join("  ");
    println!("by level: {level}");
    let cat = c
        .by_category
        .iter()
        .map(|(k, v)| format!("{k} {v}"))
        .collect::<Vec<_>>()
        .join("  ");
    println!("by category: {cat}");

    if !report.warnings.is_empty() {
        println!("\n{} warning(s):", report.warnings.len());
        for w in &report.warnings {
            println!("  ! {w}");
        }
    }

    if report.ok() {
        println!("\nStatus: PASS");
    } else {
        println!("\n{} error(s):", report.errors.len());
        for e in &report.errors {
            println!("  - {e}");
        }
        println!("Status: FAIL");
    }
}

fn print_help() {
    println!("srs-site — parse, validate, and render the Varro contribution-spec\n");
    println!("USAGE:");
    println!("  srs-site check    [--spec <dir>]");
    println!("  srs-site generate [--spec <dir>] [--out <dir>]\n");
    println!("DEFAULTS: --spec varro   --out site");
    println!("EXIT:     0 ok · 1 spec invalid · 3 environment/usage error");
}
