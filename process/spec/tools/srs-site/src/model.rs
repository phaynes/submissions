//! Typed model of a parsed contribution-spec document.
//!
//! A [`Spec`] is one `system` header (metadata, closed `enum`s, and the
//! `type Requirement` schema) plus a flat list of [`Requirement`] instances that the
//! validator checks against that schema.

use std::collections::BTreeMap;

/// A field value inside a `requirement` block. The *kind* is decided at parse time by
/// the token that follows the field name, so the validator can check it against the
/// declared field type: a bare word must line up with an enum-/ident-typed field, a
/// quoted string with a text field (`string`/`markdown`/`uri`), and a `[ … ]` list
/// with a `list` field.
#[derive(Debug, Clone)]
pub enum Value {
    /// A bare word, e.g. `both` in `project both`.
    Word(String),
    /// A quoted string, e.g. the `statement "…"`.
    Text(String),
    /// A bracketed list of strings, e.g. `acceptance [ "…", "…" ]`.
    List(Vec<String>),
}

/// One field of the `type Requirement` schema, e.g. `field level: Level required`.
#[derive(Debug, Clone)]
pub struct FieldDef {
    pub name: String,
    /// The declared type: `ident`, `string`, `markdown`, `uri`, `list`, or an enum name.
    pub type_ref: String,
    pub required: bool,
}

/// A `type <Name> { … }` block.
#[derive(Debug, Clone, Default)]
pub struct TypeDef {
    pub name: String,
    pub fields: Vec<FieldDef>,
}

/// The `system … { … }` header: metadata, closed vocabularies, and type schemas.
#[derive(Debug, Clone, Default)]
pub struct SystemMeta {
    pub name: String,
    pub mission: Option<String>,
    pub authority: Option<String>,
    pub domain: Option<String>,
    pub maturity: Option<String>,
    /// enum name -> its ordered variants.
    pub enums: BTreeMap<String, Vec<String>>,
    /// type name -> its schema.
    pub types: BTreeMap<String, TypeDef>,
}

/// One `requirement <ID> { … }` instance.
#[derive(Debug, Clone)]
pub struct Requirement {
    /// The unique ID from the block header, e.g. `STY-001`.
    pub id: String,
    /// Field name -> value, in declaration order preserved by the parser via BTreeMap
    /// keys (lookup is by name; render order is imposed by the generator).
    pub fields: BTreeMap<String, Value>,
    /// 1-based line of the `requirement` keyword, for error messages.
    pub line: usize,
}

impl Requirement {
    /// The value of a `Word` field (`project`, `category`, `level`), if present.
    pub fn word(&self, k: &str) -> Option<&str> {
        match self.fields.get(k) {
            Some(Value::Word(s)) => Some(s.as_str()),
            _ => None,
        }
    }

    /// The value of a `Text` field (`title`, `source`, `statement`, …), if present.
    pub fn text(&self, k: &str) -> Option<&str> {
        match self.fields.get(k) {
            Some(Value::Text(s)) => Some(s.as_str()),
            _ => None,
        }
    }

    /// The items of a `List` field (`acceptance`), if present.
    pub fn list(&self, k: &str) -> Option<&[String]> {
        match self.fields.get(k) {
            Some(Value::List(v)) => Some(v.as_slice()),
            _ => None,
        }
    }
}

/// A whole parsed document.
#[derive(Debug, Clone, Default)]
pub struct Spec {
    pub system: SystemMeta,
    pub requirements: Vec<Requirement>,
}
