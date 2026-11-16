//! Textual tree-shaking of a WAT module: keep imports, memories, data and the functions and
//! globals reachable (by `call $f`, `global.get/set $g`) from the given roots; drop inline
//! exports of the dropped-to-internal functions. Comments preceding a field stay with it.
//! (Only for the regular WAT written in this directory: named functions/globals, no tables.)

use std::collections::{BTreeMap, BTreeSet};

/// Split `(module ...)` into (prefix, fields, suffix); each field keeps its leading comments.
fn fields(text: &str) -> (String, Vec<String>, String) {
    let b = text.as_bytes();
    let start = text.find("(module").expect("(module") + "(module".len();
    let (mut i, mut depth, mut cur, mut out) = (start, 0i32, String::new(), vec![]);
    let mut field_start = start;
    let mut pending_from = start;
    while i < b.len() {
        if b[i] == b';' && i + 1 < b.len() && b[i + 1] == b';' {
            let e = text[i..].find('\n').map(|k| i + k + 1).unwrap_or(b.len());
            i = e;
            continue;
        }
        if b[i] == b'"' {
            i += 1;
            while b[i] != b'"' {
                if b[i] == b'\\' {
                    i += 1;
                }
                i += 1;
            }
            i += 1;
            continue;
        }
        if b[i] == b'(' {
            if depth == 0 {
                field_start = pending_from;
            }
            depth += 1;
        } else if b[i] == b')' {
            if depth == 0 {
                // end of module
                let _ = cur;
                return (
                    text[..start].to_string(),
                    out,
                    text[field_start.max(pending_from)..].to_string(),
                );
            }
            depth -= 1;
            if depth == 0 {
                // include the rest of the line (trailing comment)
                let e = text[i..].find('\n').map(|k| i + k + 1).unwrap_or(b.len());
                out.push(text[field_start..e].to_string());
                pending_from = e;
                i = e;
                cur = String::new();
                continue;
            }
        }
        i += 1;
    }
    panic!("unbalanced module");
}

fn head(field: &str) -> (String, Option<String>) {
    // kind and $name of a field
    let t = field
        .lines()
        .skip_while(|l| l.trim_start().starts_with(";;") || l.trim().is_empty())
        .collect::<Vec<_>>()
        .join("\n");
    let t = t.trim_start().trim_start_matches('(');
    let mut it = t.split_whitespace();
    let kind = it.next().unwrap_or("").to_string();
    let name = it
        .next()
        .filter(|n| n.starts_with('$'))
        .map(|n| n.trim_end_matches(')').to_string());
    (kind, name)
}

fn refs(field: &str) -> BTreeSet<String> {
    let mut s = BTreeSet::new();
    for pat in ["call $", "global.get $", "global.set $"] {
        let mut rest = field;
        while let Some(k) = rest.find(pat) {
            let r = &rest[k + pat.len() - 1..];
            let e = r
                .find(|c: char| c.is_whitespace() || c == ')')
                .unwrap_or(r.len());
            s.insert(r[..e].to_string());
            rest = &r[e..];
        }
    }
    s
}

/// Keep what is reachable from `roots` ($names) and from every exported function in
/// `keep_exports`; drop other inline exports.
pub fn prune(text: &str, roots: &[&str]) -> String {
    let (pre, fs, post) = fields(text);
    let names: BTreeMap<String, usize> = fs
        .iter()
        .enumerate()
        .filter_map(|(i, f)| head(f).1.map(|n| (n, i)))
        .collect();
    let mut keep: BTreeSet<usize> = BTreeSet::new();
    let mut work: Vec<String> = roots.iter().map(|s| s.to_string()).collect();
    for (i, f) in fs.iter().enumerate() {
        let (k, _) = head(f);
        if k == "import" || k == "memory" || k == "data" {
            keep.insert(i);
            work.extend(refs(f));
        }
    }
    while let Some(n) = work.pop() {
        if let Some(&i) = names.get(&n)
            && keep.insert(i)
        {
            work.extend(refs(&fs[i]));
        }
    }
    let rootset: BTreeSet<&str> = roots.iter().copied().collect();
    let mut out = pre;
    out.push('\n');
    for (i, f) in fs.iter().enumerate() {
        if !keep.contains(&i) {
            continue;
        }
        let (k, n) = head(f);
        let mut f = f.clone();
        if k == "func" && n.as_deref().is_some_and(|n| !rootset.contains(n)) {
            // drop an inline export: `(export "x") ` after the name
            if let Some(p) = f.find(" (export \"") {
                let e = f[p + 10..].find("\")").map(|k| p + 10 + k + 2).unwrap();
                f.replace_range(p..e, "");
            }
        }
        out += &f;
    }
    out += &post;
    out
}
