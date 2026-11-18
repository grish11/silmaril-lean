//! Minimal S-expressions for contract terms (SMT-LIB syntax).

use anyhow::{Result, bail};

#[derive(Clone, Debug, PartialEq)]
pub enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

pub fn parse(s: &str) -> Result<Sexp> {
    let toks: Vec<String> = s
        .replace('(', " ( ")
        .replace(')', " ) ")
        .split_whitespace()
        .map(String::from)
        .collect();
    let mut i = 0;
    let e = parse_at(&toks, &mut i)?;
    if i != toks.len() {
        bail!("trailing tokens in {s}");
    }
    Ok(e)
}

fn parse_at(t: &[String], i: &mut usize) -> Result<Sexp> {
    let Some(tok) = t.get(*i) else {
        bail!("unexpected end")
    };
    *i += 1;
    if tok == "(" {
        let mut v = vec![];
        while t.get(*i).map(String::as_str) != Some(")") {
            if *i >= t.len() {
                bail!("unbalanced");
            }
            v.push(parse_at(t, i)?);
        }
        *i += 1;
        Ok(Sexp::List(v))
    } else if tok == ")" {
        bail!("unexpected )")
    } else {
        Ok(Sexp::Atom(tok.clone()))
    }
}

impl std::fmt::Display for Sexp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sexp::Atom(a) => write!(f, "{a}"),
            Sexp::List(v) => {
                write!(f, "(")?;
                for (k, x) in v.iter().enumerate() {
                    if k > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{x}")?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Sexp {
    pub fn head(&self) -> Option<&str> {
        match self {
            Sexp::List(v) => match v.first() {
                Some(Sexp::Atom(a)) => Some(a),
                _ => None,
            },
            _ => None,
        }
    }
    pub fn args(&self) -> &[Sexp] {
        match self {
            Sexp::List(v) => &v[1..],
            _ => &[],
        }
    }
    /// Bottom-up rewrite.
    pub fn map(&self, f: &impl Fn(&Sexp) -> Option<Sexp>) -> Sexp {
        if let Some(r) = f(self) {
            return r;
        }
        match self {
            Sexp::List(v) => Sexp::List(v.iter().map(|x| x.map(f)).collect()),
            a => a.clone(),
        }
    }
}
