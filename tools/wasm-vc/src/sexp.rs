//! S-expressions for WAT text and SMT-LIB-style annotation terms.

use anyhow::{Result, bail};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sexp {
    Atom(String),
    Str(String),
    List(Vec<Sexp>),
}

impl Sexp {
    pub fn atom(&self) -> Option<&str> {
        match self {
            Sexp::Atom(a) => Some(a),
            _ => None,
        }
    }

    pub fn list(&self) -> Option<&[Sexp]> {
        match self {
            Sexp::List(l) => Some(l),
            _ => None,
        }
    }

    /// The head atom of a list.
    pub fn head(&self) -> Option<&str> {
        self.list().and_then(|l| l.first()).and_then(Sexp::atom)
    }
}

impl fmt::Display for Sexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sexp::Atom(a) => write!(f, "{a}"),
            Sexp::Str(s) => write!(f, "{s:?}"),
            Sexp::List(l) => {
                write!(f, "(")?;
                for (i, x) in l.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{x}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// A `;; @key rest` annotation comment and the byte offset where it occurs.
#[derive(Clone, Debug)]
pub struct Annotation {
    pub offset: usize,
    pub key: String,
    pub text: String,
}

struct Parser<'a> {
    src: &'a str,
    pos: usize,
    annotations: Vec<Annotation>,
}

impl<'a> Parser<'a> {
    fn skip(&mut self) -> Result<()> {
        loop {
            let rest = &self.src[self.pos..];
            if let Some(c) = rest.chars().next()
                && c.is_whitespace()
            {
                self.pos += c.len_utf8();
            } else if rest.starts_with(";;") {
                let end = rest.find('\n').unwrap_or(rest.len());
                let line = rest[2..end].trim();
                if let Some(ann) = line.strip_prefix('@') {
                    let (key, text) = ann.split_once(char::is_whitespace).unwrap_or((ann, ""));
                    self.annotations.push(Annotation {
                        offset: self.pos,
                        key: key.to_string(),
                        text: text.trim().to_string(),
                    });
                }
                self.pos += end;
            } else if rest.starts_with("(;") {
                let Some(end) = rest.find(";)") else {
                    bail!("unterminated block comment at byte {}", self.pos);
                };
                self.pos += end + 2;
            } else {
                return Ok(());
            }
        }
    }

    fn parse(&mut self) -> Result<Sexp> {
        self.skip()?;
        let start = self.pos;
        let rest = &self.src[self.pos..];
        let Some(c) = rest.chars().next() else {
            bail!("unexpected end of input");
        };
        match c {
            '(' => {
                self.pos += 1;
                let mut items = Vec::new();
                loop {
                    self.skip()?;
                    if self.src[self.pos..].starts_with(')') {
                        self.pos += 1;
                        return Ok(Sexp::List(items));
                    }
                    if self.pos >= self.src.len() {
                        bail!("unbalanced parenthesis opened at byte {start}");
                    }
                    items.push(self.parse()?);
                }
            }
            ')' => bail!("unexpected ')' at byte {start}"),
            '"' => {
                let mut out = String::new();
                let mut chars = rest[1..].char_indices();
                while let Some((i, c)) = chars.next() {
                    match c {
                        '"' => {
                            self.pos += i + 2;
                            return Ok(Sexp::Str(out));
                        }
                        '\\' => {
                            if let Some((_, e)) = chars.next() {
                                out.push(e);
                            }
                        }
                        c => out.push(c),
                    }
                }
                bail!("unterminated string at byte {start}")
            }
            _ => {
                let end = rest
                    .find(|c: char| c.is_whitespace() || c == '(' || c == ')' || c == ';')
                    .unwrap_or(rest.len());
                self.pos += end;
                Ok(Sexp::Atom(rest[..end].to_string()))
            }
        }
    }
}

/// Parse one top-level s-expression and collect the annotation comments.
pub fn parse_with_annotations(src: &str) -> Result<(Sexp, Vec<Annotation>)> {
    let mut p = Parser {
        src,
        pos: 0,
        annotations: Vec::new(),
    };
    let top = p.parse()?;
    p.skip()?;
    if p.pos != src.len() {
        bail!("trailing input at byte {}", p.pos);
    }
    Ok((top, p.annotations))
}

/// Parse a single term (an annotation body).
pub fn parse(src: &str) -> Result<Sexp> {
    Ok(parse_with_annotations(src)?.0)
}

/// Offsets of the `(func …)` fields of a module, in order, for attaching
/// annotations to the function that follows them.
pub fn func_offsets(src: &str) -> Vec<usize> {
    let mut out = Vec::new();
    let bytes = src.as_bytes();
    let mut i = 0;
    while let Some(j) = src[i..].find("(func") {
        let at = i + j;
        let after = bytes.get(at + 5).copied().unwrap_or(b' ');
        let before_comment = src[..at].rfind('\n').map_or(0, |n| n + 1);
        if (after as char).is_whitespace() && !src[before_comment..at].contains(";;") {
            out.push(at);
        }
        i = at + 5;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_lists_strings_and_annotations() {
        let (s, anns) = parse_with_annotations(
            "(module ;; @requires true\n (func $f (export \"f\") (; c ;) (i32.const 1)))",
        )
        .unwrap();
        assert_eq!(s.head(), Some("module"));
        assert_eq!(anns.len(), 1);
        assert_eq!(anns[0].key, "requires");
        assert_eq!(anns[0].text, "true");
        assert_eq!(
            parse("(bvadd x #x00000001)").unwrap().to_string(),
            "(bvadd x #x00000001)"
        );
        assert!(parse("(a").is_err());
    }
}
