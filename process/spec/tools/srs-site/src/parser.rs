//! A small hand-rolled parser for the Varro requirements DSL.
//!
//! Grammar (EBNF-ish):
//! ```text
//!   document    = item* ;
//!   item        = system | requirement ;
//!   system      = "system" IDENT "{" sys_item* "}" ;
//!   sys_item    = "mission" STRING
//!               | "authority" "lane" STRING
//!               | "domain" IDENT
//!               | "maturity" IDENT
//!               | "enum" IDENT "{" IDENT ("," IDENT)* "}"
//!               | "type" IDENT "{" field* "}" ;
//!   field       = "field" IDENT ":" IDENT ("required" | "optional") ;
//!   requirement = "requirement" IDENT "{" req_field* "}" ;
//!   req_field   = IDENT value ;
//!   value       = STRING | IDENT | "[" STRING ("," STRING)* "]" ;
//! ```
//! Comments run from `//` to end of line (outside strings). Strings are double-quoted
//! with `\n`, `\t`, `\"`, `\\` escapes; other bytes (including multi-byte UTF-8 math
//! symbols) are copied verbatim.

use crate::model::*;
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Ident(String),
    Str(String),
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Colon,
    Comma,
}

struct Lexed {
    tok: Tok,
    line: usize,
}

/// A parse or lex failure, with the 1-based line it occurred on.
#[derive(Debug)]
pub struct ParseError {
    pub line: usize,
    pub msg: String,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "line {}: {}", self.line, self.msg)
    }
}

fn is_ident_start(c: u8) -> bool {
    c.is_ascii_alphabetic() || c == b'_'
}

fn is_ident_char(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_' || c == b'.' || c == b'-'
}

/// Byte length of a UTF-8 sequence from its leading byte.
fn utf8_len(b: u8) -> usize {
    if b < 0x80 {
        1
    } else if b >> 5 == 0b110 {
        2
    } else if b >> 4 == 0b1110 {
        3
    } else if b >> 3 == 0b11110 {
        4
    } else {
        1
    }
}

fn lex(src: &str) -> Result<Vec<Lexed>, ParseError> {
    let mut out = Vec::new();
    let bytes = src.as_bytes();
    let mut i = 0;
    let mut line = 1usize;
    while i < bytes.len() {
        let c = bytes[i];
        match c {
            b'\n' => {
                line += 1;
                i += 1;
            }
            b' ' | b'\t' | b'\r' => i += 1,
            b'/' if i + 1 < bytes.len() && bytes[i + 1] == b'/' => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'{' => {
                out.push(Lexed { tok: Tok::LBrace, line });
                i += 1;
            }
            b'}' => {
                out.push(Lexed { tok: Tok::RBrace, line });
                i += 1;
            }
            b'[' => {
                out.push(Lexed { tok: Tok::LBracket, line });
                i += 1;
            }
            b']' => {
                out.push(Lexed { tok: Tok::RBracket, line });
                i += 1;
            }
            b':' => {
                out.push(Lexed { tok: Tok::Colon, line });
                i += 1;
            }
            b',' => {
                out.push(Lexed { tok: Tok::Comma, line });
                i += 1;
            }
            b'"' => {
                i += 1;
                let start_line = line;
                let mut s = String::new();
                loop {
                    if i >= bytes.len() {
                        return Err(ParseError { line: start_line, msg: "unterminated string".into() });
                    }
                    match bytes[i] {
                        b'"' => {
                            i += 1;
                            break;
                        }
                        b'\\' => {
                            i += 1;
                            if i >= bytes.len() {
                                return Err(ParseError { line: start_line, msg: "dangling escape".into() });
                            }
                            match bytes[i] {
                                b'n' => s.push('\n'),
                                b't' => s.push('\t'),
                                b'"' => s.push('"'),
                                b'\\' => s.push('\\'),
                                other => {
                                    s.push('\\');
                                    s.push(other as char);
                                }
                            }
                            i += 1;
                        }
                        b'\n' => {
                            s.push('\n');
                            line += 1;
                            i += 1;
                        }
                        b => {
                            let n = utf8_len(b);
                            let end = (i + n).min(bytes.len());
                            s.push_str(std::str::from_utf8(&bytes[i..end]).unwrap_or("\u{FFFD}"));
                            i = end;
                        }
                    }
                }
                out.push(Lexed { tok: Tok::Str(s), line: start_line });
            }
            _ if is_ident_start(c) => {
                let start = i;
                while i < bytes.len() && is_ident_char(bytes[i]) {
                    i += 1;
                }
                let word = std::str::from_utf8(&bytes[start..i]).unwrap_or("").to_string();
                out.push(Lexed { tok: Tok::Ident(word), line });
            }
            _ => {
                return Err(ParseError { line, msg: format!("unexpected character '{}'", c as char) });
            }
        }
    }
    Ok(out)
}

struct Parser {
    toks: Vec<Lexed>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|l| &l.tok)
    }

    fn line(&self) -> usize {
        self.toks
            .get(self.pos)
            .or_else(|| self.toks.last())
            .map(|l| l.line)
            .unwrap_or(0)
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn err(&self, msg: impl Into<String>) -> ParseError {
        ParseError { line: self.line(), msg: msg.into() }
    }

    fn expect(&mut self, want: &Tok) -> Result<(), ParseError> {
        match self.peek() {
            Some(t) if t == want => {
                self.advance();
                Ok(())
            }
            Some(t) => Err(self.err(format!("expected {want:?}, found {t:?}"))),
            None => Err(self.err(format!("expected {want:?}, found end of input"))),
        }
    }

    fn expect_ident(&mut self) -> Result<String, ParseError> {
        match self.peek() {
            Some(Tok::Ident(s)) => {
                let s = s.clone();
                self.advance();
                Ok(s)
            }
            other => Err(self.err(format!("expected identifier, found {other:?}"))),
        }
    }

    fn expect_str(&mut self) -> Result<String, ParseError> {
        match self.peek() {
            Some(Tok::Str(s)) => {
                let s = s.clone();
                self.advance();
                Ok(s)
            }
            other => Err(self.err(format!("expected string, found {other:?}"))),
        }
    }

    fn expect_kw(&mut self, kw: &str) -> Result<(), ParseError> {
        let id = self.expect_ident()?;
        if id != kw {
            return Err(self.err(format!("expected `{kw}`, found `{id}`")));
        }
        Ok(())
    }

    fn parse_system(&mut self) -> Result<SystemMeta, ParseError> {
        self.expect_kw("system")?;
        let name = self.expect_ident()?;
        self.expect(&Tok::LBrace)?;
        let mut meta = SystemMeta { name, ..Default::default() };
        loop {
            match self.peek() {
                Some(Tok::RBrace) => {
                    self.advance();
                    break;
                }
                Some(Tok::Ident(k)) => {
                    let k = k.clone();
                    self.advance();
                    match k.as_str() {
                        "mission" => meta.mission = Some(self.expect_str()?),
                        "authority" => {
                            self.expect_kw("lane")?;
                            meta.authority = Some(self.expect_str()?);
                        }
                        "domain" => meta.domain = Some(self.expect_ident()?),
                        "maturity" => meta.maturity = Some(self.expect_ident()?),
                        "enum" => {
                            let (n, vs) = self.parse_enum()?;
                            meta.enums.insert(n, vs);
                        }
                        "type" => {
                            let t = self.parse_type()?;
                            meta.types.insert(t.name.clone(), t);
                        }
                        other => return Err(self.err(format!("unknown system directive `{other}`"))),
                    }
                }
                _ => return Err(self.err("expected a system directive or `}`")),
            }
        }
        Ok(meta)
    }

    fn parse_enum(&mut self) -> Result<(String, Vec<String>), ParseError> {
        let name = self.expect_ident()?;
        self.expect(&Tok::LBrace)?;
        let mut vs = Vec::new();
        loop {
            match self.peek() {
                Some(Tok::RBrace) => {
                    self.advance();
                    break;
                }
                Some(Tok::Comma) => self.advance(),
                Some(Tok::Ident(v)) => {
                    vs.push(v.clone());
                    self.advance();
                }
                _ => return Err(self.err("expected an enum variant or `}`")),
            }
        }
        Ok((name, vs))
    }

    fn parse_type(&mut self) -> Result<TypeDef, ParseError> {
        let name = self.expect_ident()?;
        self.expect(&Tok::LBrace)?;
        let mut t = TypeDef { name, fields: Vec::new() };
        loop {
            match self.peek() {
                Some(Tok::RBrace) => {
                    self.advance();
                    break;
                }
                Some(Tok::Ident(k)) if k == "field" => {
                    self.advance();
                    let fname = self.expect_ident()?;
                    self.expect(&Tok::Colon)?;
                    let tref = self.expect_ident()?;
                    let req = self.expect_ident()?;
                    let required = match req.as_str() {
                        "required" => true,
                        "optional" => false,
                        other => {
                            return Err(self.err(format!("expected `required`/`optional`, found `{other}`")))
                        }
                    };
                    t.fields.push(FieldDef { name: fname, type_ref: tref, required });
                }
                _ => return Err(self.err("expected `field` or `}`")),
            }
        }
        Ok(t)
    }

    fn parse_requirement(&mut self) -> Result<Requirement, ParseError> {
        let line = self.line();
        self.expect_kw("requirement")?;
        let id = self.expect_ident()?;
        self.expect(&Tok::LBrace)?;
        let mut fields: BTreeMap<String, Value> = BTreeMap::new();
        loop {
            match self.peek() {
                Some(Tok::RBrace) => {
                    self.advance();
                    break;
                }
                Some(Tok::Ident(k)) => {
                    let k = k.clone();
                    self.advance();
                    let v = self.parse_value()?;
                    if fields.insert(k.clone(), v).is_some() {
                        return Err(self.err(format!("duplicate field `{k}` in requirement `{id}`")));
                    }
                }
                _ => return Err(self.err("expected a field name or `}`")),
            }
        }
        Ok(Requirement { id, fields, line })
    }

    fn parse_value(&mut self) -> Result<Value, ParseError> {
        match self.peek() {
            Some(Tok::Str(s)) => {
                let s = s.clone();
                self.advance();
                Ok(Value::Text(s))
            }
            Some(Tok::Ident(s)) => {
                let s = s.clone();
                self.advance();
                Ok(Value::Word(s))
            }
            Some(Tok::LBracket) => {
                self.advance();
                let mut items = Vec::new();
                loop {
                    match self.peek() {
                        Some(Tok::RBracket) => {
                            self.advance();
                            break;
                        }
                        Some(Tok::Comma) => self.advance(),
                        Some(Tok::Str(s)) => {
                            items.push(s.clone());
                            self.advance();
                        }
                        _ => return Err(self.err("expected a string or `]` in list")),
                    }
                }
                Ok(Value::List(items))
            }
            other => Err(self.err(format!("expected a value (string, word, or list), found {other:?}"))),
        }
    }
}

/// Parse one DSL document (which may contain a `system` block and/or `requirement`s).
pub fn parse(src: &str) -> Result<Spec, ParseError> {
    let toks = lex(src)?;
    let mut p = Parser { toks, pos: 0 };
    let mut spec = Spec::default();
    let mut saw_system = false;
    while let Some(t) = p.peek() {
        match t {
            Tok::Ident(k) if k == "system" => {
                if saw_system {
                    return Err(p.err("more than one `system` block in a single file"));
                }
                saw_system = true;
                spec.system = p.parse_system()?;
            }
            Tok::Ident(k) if k == "requirement" => {
                let r = p.parse_requirement()?;
                spec.requirements.push(r);
            }
            Tok::Ident(k) => {
                let k = k.clone();
                return Err(p.err(format!("expected `system` or `requirement`, found `{k}`")));
            }
            _ => return Err(p.err("expected a top-level `system` or `requirement`")),
        }
    }
    Ok(spec)
}
