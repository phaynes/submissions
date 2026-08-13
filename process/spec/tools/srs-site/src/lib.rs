//! contribution-spec toolchain: parse the Varro requirements DSL, validate it
//! fail-closed, and render a Quarto website.
//!
//! The library is split so the binary and the integration tests share one code path:
//! [`load_dir`] reads a directory of `.varro` files into a [`model::Spec`],
//! [`validate::validate`] checks it, and [`generate::generate`] renders it.

pub mod generate;
pub mod model;
pub mod parser;
pub mod validate;

use std::path::{Path, PathBuf};

/// Failure loading a spec directory. `code` follows the fail-closed exit taxonomy:
/// `3` = environment/IO (missing or unreadable input — never a false green),
/// `1` = content (a malformed or self-inconsistent spec).
#[derive(Debug)]
pub struct LoadError {
    pub code: i32,
    pub msg: String,
}

/// Read every `*.varro` file in `dir` (sorted), parse each, and merge into one
/// [`model::Spec`]. Exactly one `system` block must be present across the fileset.
pub fn load_dir(dir: &Path) -> Result<model::Spec, LoadError> {
    let mut files: Vec<PathBuf> = match std::fs::read_dir(dir) {
        Ok(rd) => rd
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.extension().map(|x| x == "varro").unwrap_or(false))
            .collect(),
        Err(e) => {
            return Err(LoadError { code: 3, msg: format!("cannot read spec dir {}: {e}", dir.display()) })
        }
    };
    files.sort();
    if files.is_empty() {
        return Err(LoadError { code: 3, msg: format!("no .varro files in {}", dir.display()) });
    }

    let mut merged = model::Spec::default();
    let mut system_file: Option<PathBuf> = None;
    for f in &files {
        let src = match std::fs::read_to_string(f) {
            Ok(s) => s,
            Err(e) => return Err(LoadError { code: 3, msg: format!("cannot read {}: {e}", f.display()) }),
        };
        let spec = parser::parse(&src)
            .map_err(|pe| LoadError { code: 1, msg: format!("{}: {pe}", f.display()) })?;
        if !spec.system.name.is_empty() {
            if let Some(prev) = &system_file {
                return Err(LoadError {
                    code: 1,
                    msg: format!("more than one `system` block ({} and {})", prev.display(), f.display()),
                });
            }
            merged.system = spec.system;
            system_file = Some(f.clone());
        }
        merged.requirements.extend(spec.requirements);
    }
    if system_file.is_none() {
        return Err(LoadError { code: 1, msg: "no `system` block found in any .varro file".into() });
    }
    Ok(merged)
}
