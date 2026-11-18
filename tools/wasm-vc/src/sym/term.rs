//! Hash-consed SMT terms (bit-vectors, Booleans, byte arrays, histories) with
//! constant folding and local simplifications, printed as SMT-LIB.
//!
//! Every constructor simplifies; the simplifications are the usual bit-vector
//! identities and are what make dispatch on constants (`br_table` on a known
//! register index, flags stored as `0`/`1`) collapse during symbolic execution.

use std::collections::HashMap;
use std::fmt::Write;

pub type Id = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Sort {
    Bool,
    Bv(u32),
    /// `(Array (_ BitVec aw) (_ BitVec 8))`: a byte-addressed memory.
    Mem(u32),
    /// The datatype of import-call histories.
    Hist,
}

impl Sort {
    pub fn smt(self) -> String {
        match self {
            Sort::Bool => "Bool".into(),
            Sort::Bv(w) => format!("(_ BitVec {w})"),
            Sort::Mem(aw) => format!("(Array (_ BitVec {aw}) (_ BitVec 8))"),
            Sort::Hist => "Hist".into(),
        }
    }
    pub fn width(self) -> u32 {
        match self {
            Sort::Bv(w) => w,
            _ => panic!("not a bit-vector sort: {self:?}"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Bv2 {
    Add,
    Sub,
    Mul,
    Udiv,
    Urem,
    Sdiv,
    Srem,
    And,
    Or,
    Xor,
    Shl,
    Lshr,
    Ashr,
}

impl Bv2 {
    fn smt(self) -> &'static str {
        match self {
            Bv2::Add => "bvadd",
            Bv2::Sub => "bvsub",
            Bv2::Mul => "bvmul",
            Bv2::Udiv => "bvudiv",
            Bv2::Urem => "bvurem",
            Bv2::Sdiv => "bvsdiv",
            Bv2::Srem => "bvsrem",
            Bv2::And => "bvand",
            Bv2::Or => "bvor",
            Bv2::Xor => "bvxor",
            Bv2::Shl => "bvshl",
            Bv2::Lshr => "bvlshr",
            Bv2::Ashr => "bvashr",
        }
    }
    fn commutative(self) -> bool {
        matches!(self, Bv2::Add | Bv2::Mul | Bv2::And | Bv2::Or | Bv2::Xor)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Rel {
    Ult,
    Ule,
    Slt,
    Sle,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum N {
    Var(String, Sort),
    /// Bit-vector literal (width ≤ 64).
    Lit(u64, u32),
    True,
    False,
    Not(Id),
    And(Vec<Id>),
    Or(Vec<Id>),
    Ite(Id, Id, Id),
    Eq(Id, Id),
    Bin(Bv2, Id, Id),
    Rel(Rel, Id, Id),
    Extract(u32, u32, Id),
    Zext(u32, Id),
    Sext(u32, Id),
    Concat(Id, Id),
    /// The constant array with every byte equal to the literal.
    ConstMem(u8, u32),
    Select(Id, Id),
    Store(Id, Id, Id),
    /// `memory.copy`: destination memory, source memory, dst, src, n (all 32-bit).
    Copy(Id, Id, Id, Id, Id),
    /// `memory.fill`: memory, dst, byte, n.
    Fill(Id, Id, Id, Id),
    /// Application of an uninterpreted function.
    App(String, Vec<Id>, Sort),
    HistNil,
    /// One import call: import number, arguments (7 × 64 bits, zero padded), previous.
    HistCons(u32, Vec<Id>, Id),
    /// SMT-LIB text of the given sort over names bound to terms (`let`).
    Raw(String, Vec<(String, Id)>, Sort),
}

pub fn mask(w: u32) -> u64 {
    if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
}

fn sext(v: u64, w: u32) -> i64 {
    if w >= 64 {
        v as i64
    } else {
        ((v << (64 - w)) as i64) >> (64 - w)
    }
}

#[derive(Default)]
pub struct Terms {
    nodes: Vec<N>,
    sorts: Vec<Sort>,
    table: HashMap<N, Id>,
    fresh: u64,
    sel_cache: HashMap<(Id, Id), Id>,
    ext_cache: HashMap<(u32, u32, Id), Id>,
}

/// Bound on the leaves of `ite` trees of literals that operations distribute over.
pub const LIT_ITE_LEAVES: i32 = 64;

pub const HIST_ARGS: usize = 7;

impl Terms {
    pub fn new() -> Self {
        Terms::default()
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn node(&self, t: Id) -> &N {
        &self.nodes[t as usize]
    }

    pub fn sort(&self, t: Id) -> Sort {
        self.sorts[t as usize]
    }

    pub fn width(&self, t: Id) -> u32 {
        self.sort(t).width()
    }

    fn intern(&mut self, n: N, s: Sort) -> Id {
        if let Some(&i) = self.table.get(&n) {
            return i;
        }
        let i = self.nodes.len() as Id;
        self.nodes.push(n.clone());
        self.sorts.push(s);
        self.table.insert(n, i);
        i
    }

    pub fn var(&mut self, name: &str, s: Sort) -> Id {
        self.intern(N::Var(name.to_string(), s), s)
    }

    /// A variable with a fresh name `prefix!n`.
    pub fn fresh(&mut self, prefix: &str, s: Sort) -> Id {
        self.fresh += 1;
        let n = format!("{prefix}!{}", self.fresh);
        self.var(&n, s)
    }

    /// SMT-LIB text with names bound to terms; `true`/`false` texts fold.
    pub fn raw_let(&mut self, text: &str, binds: Vec<(String, Id)>, s: Sort) -> Id {
        match text.trim() {
            "true" if s == Sort::Bool => return self.tt(),
            "false" if s == Sort::Bool => return self.ff(),
            _ => {}
        }
        // keep only the names the text mentions
        let toks: std::collections::HashSet<&str> = text
            .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
            .filter(|t| !t.is_empty())
            .collect();
        let mut b: Vec<(String, Id)> = binds
            .into_iter()
            .filter(|(n, _)| toks.contains(n.as_str()) || toks.contains(quote(n).as_str()))
            .collect();
        b.sort();
        b.dedup_by(|x, y| x.0 == y.0);
        self.intern(N::Raw(text.to_string(), b, s), s)
    }

    pub fn lit(&mut self, v: u64, w: u32) -> Id {
        self.intern(N::Lit(v & mask(w), w), Sort::Bv(w))
    }

    pub fn tt(&mut self) -> Id {
        self.intern(N::True, Sort::Bool)
    }

    pub fn ff(&mut self) -> Id {
        self.intern(N::False, Sort::Bool)
    }

    pub fn boolean(&mut self, b: bool) -> Id {
        if b { self.tt() } else { self.ff() }
    }

    pub fn as_lit(&self, t: Id) -> Option<u64> {
        match self.node(t) {
            N::Lit(v, _) => Some(*v),
            _ => None,
        }
    }

    pub fn as_bool(&self, t: Id) -> Option<bool> {
        match self.node(t) {
            N::True => Some(true),
            N::False => Some(false),
            _ => None,
        }
    }

    pub fn is_false(&self, t: Id) -> bool {
        self.as_bool(t) == Some(false)
    }

    pub fn not(&mut self, a: Id) -> Id {
        match self.node(a).clone() {
            N::True => self.ff(),
            N::False => self.tt(),
            N::Not(x) => x,
            _ => self.intern(N::Not(a), Sort::Bool),
        }
    }

    pub fn and(&mut self, xs: &[Id]) -> Id {
        let mut v = Vec::new();
        for &x in xs {
            match self.node(x).clone() {
                N::True => {}
                N::False => return self.ff(),
                N::And(ys) => v.extend(ys),
                _ => v.push(x),
            }
        }
        v.sort_unstable();
        v.dedup();
        for &x in &v {
            if let N::Not(y) = self.node(x)
                && v.binary_search(y).is_ok()
            {
                return self.ff();
            }
        }
        match v.len() {
            0 => self.tt(),
            1 => v[0],
            _ => self.intern(N::And(v), Sort::Bool),
        }
    }

    pub fn and2(&mut self, a: Id, b: Id) -> Id {
        self.and(&[a, b])
    }

    pub fn or(&mut self, xs: &[Id]) -> Id {
        let mut v = Vec::new();
        for &x in xs {
            match self.node(x).clone() {
                N::False => {}
                N::True => return self.tt(),
                N::Or(ys) => v.extend(ys),
                _ => v.push(x),
            }
        }
        v.sort_unstable();
        v.dedup();
        for &x in &v {
            if let N::Not(y) = self.node(x)
                && v.binary_search(y).is_ok()
            {
                return self.tt();
            }
        }
        match v.len() {
            0 => self.ff(),
            1 => v[0],
            _ => self.intern(N::Or(v), Sort::Bool),
        }
    }

    pub fn or2(&mut self, a: Id, b: Id) -> Id {
        self.or(&[a, b])
    }

    pub fn implies(&mut self, a: Id, b: Id) -> Id {
        let na = self.not(a);
        self.or2(na, b)
    }

    pub fn ite(&mut self, c: Id, a: Id, b: Id) -> Id {
        if a == b {
            return a;
        }
        match self.node(c).clone() {
            N::True => return a,
            N::False => return b,
            N::Not(c2) => return self.ite(c2, b, a),
            _ => {}
        }
        let s = self.sort(a);
        if s == Sort::Bool {
            // ite(c, a, b) = (c ∧ a) ∨ (¬c ∧ b), with the constant cases folded
            match (self.as_bool(a), self.as_bool(b)) {
                (Some(true), _) => return self.or2(c, b),
                (Some(false), _) => {
                    let nc = self.not(c);
                    return self.and2(nc, b);
                }
                (_, Some(true)) => {
                    let nc = self.not(c);
                    return self.or2(nc, a);
                }
                (_, Some(false)) => return self.and2(c, a),
                _ => {}
            }
        }
        // ite(c, ite(c, x, y), b) = ite(c, x, b) and the mirror
        if let N::Ite(c2, x, _) = self.node(a).clone()
            && c2 == c
        {
            return self.ite(c, x, b);
        }
        if let N::Ite(c2, _, y) = self.node(b).clone()
            && c2 == c
        {
            return self.ite(c, a, y);
        }
        self.intern(N::Ite(c, a, b), s)
    }

    pub fn eq(&mut self, a: Id, b: Id) -> Id {
        if a == b {
            return self.tt();
        }
        let (a, b) = if a < b { (a, b) } else { (b, a) };
        match (self.node(a).clone(), self.node(b).clone()) {
            (N::Lit(x, _), N::Lit(y, _)) => return self.boolean(x == y),
            (N::True, _) => return b,
            (N::False, _) => return self.not(b),
            (_, N::True) => return a,
            (_, N::False) => return self.not(a),
            _ => {}
        }
        // ite of literals against a literal
        for (x, y) in [(a, b), (b, a)] {
            if self.as_lit(y).is_some()
                && self.lit_ite(x)
                && let N::Ite(c, p, q) = self.node(x).clone()
            {
                let p2 = self.eq(p, y);
                let q2 = self.eq(q, y);
                return self.ite(c, p2, q2);
            }
            if let (N::Ite(c, p, q), Some(k)) = (self.node(x).clone(), self.as_lit(y))
                && let (Some(pv), Some(qv)) = (self.as_lit(p), self.as_lit(q))
            {
                return match (pv == k, qv == k) {
                    (true, true) => self.tt(),
                    (true, false) => c,
                    (false, true) => self.not(c),
                    (false, false) => self.ff(),
                };
            }
            // zext(x) = k
            if let (N::Zext(n, z), Some(k)) = (self.node(x).clone(), self.as_lit(y)) {
                let w = self.width(z);
                if k >> w != 0 {
                    return self.ff();
                }
                let _ = n;
                let kk = self.lit(k, w);
                return self.eq(z, kk);
            }
        }
        self.intern(N::Eq(a, b), Sort::Bool)
    }

    pub fn ne(&mut self, a: Id, b: Id) -> Id {
        let e = self.eq(a, b);
        self.not(e)
    }

    pub fn rel(&mut self, r: Rel, a: Id, b: Id) -> Id {
        let w = self.width(a);
        if let (Some(x), Some(y)) = (self.as_lit(a), self.as_lit(b)) {
            let v = match r {
                Rel::Ult => x < y,
                Rel::Ule => x <= y,
                Rel::Slt => sext(x, w) < sext(y, w),
                Rel::Sle => sext(x, w) <= sext(y, w),
            };
            return self.boolean(v);
        }
        if a == b {
            return self.boolean(matches!(r, Rel::Ule | Rel::Sle));
        }
        for (x, y, first) in [(a, b, true), (b, a, false)] {
            if self.as_lit(y).is_some()
                && self.lit_ite(x)
                && let N::Ite(c, p, q) = self.node(x).clone()
            {
                let (p2, q2) = if first {
                    (self.rel(r, p, y), self.rel(r, q, y))
                } else {
                    (self.rel(r, y, p), self.rel(r, y, q))
                };
                return self.ite(c, p2, q2);
            }
        }
        if r == Rel::Ult && self.as_lit(b) == Some(0) {
            return self.ff();
        }
        if r == Rel::Ule && self.as_lit(a) == Some(0) {
            return self.tt();
        }
        self.intern(N::Rel(r, a, b), Sort::Bool)
    }

    pub fn bin(&mut self, op: Bv2, a: Id, b: Id) -> Id {
        let w = self.width(a);
        debug_assert_eq!(w, self.width(b), "{op:?}");
        let m = mask(w);
        let (la, lb) = (self.as_lit(a), self.as_lit(b));
        if let (Some(x), Some(y)) = (la, lb) {
            let v = match op {
                Bv2::Add => x.wrapping_add(y),
                Bv2::Sub => x.wrapping_sub(y),
                Bv2::Mul => x.wrapping_mul(y),
                Bv2::Udiv => x.checked_div(y).unwrap_or(m),
                Bv2::Urem => {
                    if y == 0 {
                        x
                    } else {
                        x % y
                    }
                }
                Bv2::Sdiv | Bv2::Srem => {
                    let (sx, sy) = (sext(x, w) as i128, sext(y, w) as i128);
                    if sy == 0 {
                        // SMT-LIB semantics for division by zero
                        if op == Bv2::Sdiv {
                            if sx < 0 { 1 } else { m }
                        } else {
                            x
                        }
                    } else if op == Bv2::Sdiv {
                        (sx / sy) as u64
                    } else {
                        (sx % sy) as u64
                    }
                }
                Bv2::And => x & y,
                Bv2::Or => x | y,
                Bv2::Xor => x ^ y,
                Bv2::Shl => {
                    if y >= w as u64 {
                        0
                    } else {
                        x << y
                    }
                }
                Bv2::Lshr => {
                    if y >= w as u64 {
                        0
                    } else {
                        x >> y
                    }
                }
                Bv2::Ashr => {
                    let s = sext(x, w);
                    (if y >= w as u64 { s >> 63 } else { s >> y }) as u64
                }
            };
            return self.lit(v & m, w);
        }
        // an operand ranging over a few literals, the other literal: distribute
        for (x, y, first) in [(a, b, true), (b, a, false)] {
            if self.as_lit(y).is_some()
                && self.lit_ite(x)
                && let N::Ite(c, p, q) = self.node(x).clone()
            {
                let (p2, q2) = if first {
                    (self.bin(op, p, y), self.bin(op, q, y))
                } else {
                    (self.bin(op, y, p), self.bin(op, y, q))
                };
                return self.ite(c, p2, q2);
            }
        }
        // canonical order for commutative operators: literal second
        let (a, b, la, lb) = if op.commutative() && (la.is_some() || (lb.is_none() && a > b)) {
            (b, a, lb, la)
        } else {
            (a, b, la, lb)
        };
        match (op, lb) {
            (
                Bv2::Add | Bv2::Sub | Bv2::Or | Bv2::Xor | Bv2::Shl | Bv2::Lshr | Bv2::Ashr,
                Some(0),
            ) => {
                return a;
            }
            (Bv2::And | Bv2::Mul, Some(0)) => return b,
            (Bv2::And, Some(k)) if k == m => return a,
            (Bv2::Or, Some(k)) if k == m => return b,
            (Bv2::Mul | Bv2::Udiv | Bv2::Sdiv, Some(1)) => return a,
            (Bv2::Shl | Bv2::Lshr, Some(k)) if k >= w as u64 => return self.lit(0, w),
            _ => {}
        }
        if la == Some(0) && matches!(op, Bv2::Shl | Bv2::Lshr | Bv2::Ashr) {
            return a;
        }
        if a == b {
            match op {
                Bv2::And | Bv2::Or => return a,
                Bv2::Xor | Bv2::Sub => return self.lit(0, w),
                _ => {}
            }
        }
        // (x op k1) op k2 for associative operators
        if let Some(k2) = lb
            && matches!(op, Bv2::Add | Bv2::And | Bv2::Or | Bv2::Xor)
            && let N::Bin(op1, x, k1) = self.node(a).clone()
            && op1 == op
            && let Some(k1) = self.as_lit(k1)
        {
            let k = self.lit(k1, w);
            let k2 = self.lit(k2, w);
            let kk = self.bin(op, k, k2);
            return self.bin(op, x, kk);
        }
        // masks of zero-extensions and ite of literals
        if op == Bv2::And
            && let Some(k) = lb
        {
            if let N::Zext(_, z) = self.node(a).clone() {
                let zw = self.width(z);
                if k & mask(zw) == mask(zw) {
                    return a;
                }
            }
            if let N::Ite(c, p, q) = self.node(a).clone()
                && self.as_lit(p).is_some()
                && self.as_lit(q).is_some()
            {
                let p2 = self.bin(op, p, b);
                let q2 = self.bin(op, q, b);
                return self.ite(c, p2, q2);
            }
            // extract low bits: x & (2^n - 1) = zext(extract(x))
            if k != 0 && k & (k + 1) == 0 {
                let n = 64 - k.leading_zeros();
                if n < w {
                    let e = self.extract(n - 1, 0, a);
                    return self.zext(w - n, e);
                }
            }
        }
        // shifts by a constant: extracts and concatenations
        if let Some(k) = lb {
            let k = k as u32;
            if k > 0 && k < w {
                match op {
                    Bv2::Lshr => {
                        let e = self.extract(w - 1, k, a);
                        return self.zext(k, e);
                    }
                    Bv2::Shl => {
                        let e = self.extract(w - 1 - k, 0, a);
                        let z = self.lit(0, k);
                        return self.concat(e, z);
                    }
                    _ => {}
                }
            }
        }
        self.intern(N::Bin(op, a, b), Sort::Bv(w))
    }

    pub fn extract(&mut self, hi: u32, lo: u32, a: Id) -> Id {
        if let Some(&r) = self.ext_cache.get(&(hi, lo, a)) {
            return r;
        }
        let r = self.extract_uncached(hi, lo, a);
        self.ext_cache.insert((hi, lo, a), r);
        r
    }

    fn extract_uncached(&mut self, hi: u32, lo: u32, a: Id) -> Id {
        let w = self.width(a);
        assert!(hi < w && lo <= hi, "extract {hi} {lo} of width {w}");
        if lo == 0 && hi == w - 1 {
            return a;
        }
        let nw = hi - lo + 1;
        match self.node(a).clone() {
            N::Lit(v, _) => self.lit(v >> lo, nw),
            N::Extract(_, lo2, b) => self.extract(hi + lo2, lo + lo2, b),
            N::Zext(_, b) | N::Sext(_, b) if hi < self.width(b) => self.extract(hi, lo, b),
            N::Zext(_, b) if lo >= self.width(b) => self.lit(0, nw),
            N::Concat(x, y) => {
                let yw = self.width(y);
                if hi < yw {
                    self.extract(hi, lo, y)
                } else if lo >= yw {
                    self.extract(hi - yw, lo - yw, x)
                } else {
                    let h = self.extract(hi - yw, 0, x);
                    let l = self.extract(yw - 1, lo, y);
                    self.concat(h, l)
                }
            }
            N::Ite(c, p, q) if self.lit_ite(a) => {
                let p2 = self.extract(hi, lo, p);
                let q2 = self.extract(hi, lo, q);
                self.ite(c, p2, q2)
            }
            N::Bin(op @ (Bv2::And | Bv2::Or | Bv2::Xor), x, y) => {
                let x2 = self.extract(hi, lo, x);
                let y2 = self.extract(hi, lo, y);
                self.bin(op, x2, y2)
            }
            N::Bin(op @ (Bv2::Add | Bv2::Sub | Bv2::Mul), x, y) if lo == 0 => {
                let x2 = self.extract(hi, 0, x);
                let y2 = self.extract(hi, 0, y);
                self.bin(op, x2, y2)
            }
            _ => self.intern(N::Extract(hi, lo, a), Sort::Bv(nw)),
        }
    }

    pub fn zext(&mut self, n: u32, a: Id) -> Id {
        if n == 0 {
            return a;
        }
        let w = self.width(a);
        match self.node(a).clone() {
            N::Lit(v, _) => self.lit(v, w + n),
            N::Zext(m, b) => self.zext(n + m, b),
            N::Ite(c, p, q) if self.lit_ite(a) => {
                let p2 = self.zext(n, p);
                let q2 = self.zext(n, q);
                self.ite(c, p2, q2)
            }
            _ => self.intern(N::Zext(n, a), Sort::Bv(w + n)),
        }
    }

    pub fn sext(&mut self, n: u32, a: Id) -> Id {
        if n == 0 {
            return a;
        }
        let w = self.width(a);
        match self.node(a).clone() {
            N::Lit(v, _) => self.lit(sext(v, w) as u64, w + n),
            N::Sext(m, b) => self.sext(n + m, b),
            N::Ite(c, p, q) if self.lit_ite(a) => {
                let p2 = self.sext(n, p);
                let q2 = self.sext(n, q);
                self.ite(c, p2, q2)
            }
            N::Zext(m, b) => self.zext(n + m, b),
            _ => self.intern(N::Sext(n, a), Sort::Bv(w + n)),
        }
    }

    pub fn concat(&mut self, hi: Id, lo: Id) -> Id {
        let (wh, wl) = (self.width(hi), self.width(lo));
        if let (Some(x), Some(y)) = (self.as_lit(hi), self.as_lit(lo))
            && wh + wl <= 64
        {
            return self.lit((x << wl) | y, wh + wl);
        }
        if self.as_lit(hi) == Some(0) {
            return self.zext(wh, lo);
        }
        // concat(extract(h1, m+1, x), extract(m, l, x)) = extract(h1, l, x)
        if let (N::Extract(h1, l1, x), N::Extract(h2, l2, y)) =
            (self.node(hi).clone(), self.node(lo).clone())
            && x == y
            && l1 == h2 + 1
        {
            return self.extract(h1, l2, x);
        }
        self.intern(N::Concat(hi, lo), Sort::Bv(wh + wl))
    }

    pub fn const_mem(&mut self, byte: u8, aw: u32) -> Id {
        self.intern(N::ConstMem(byte, aw), Sort::Mem(aw))
    }

    /// Whether `t` is a literal or an `ite` tree with literal leaves (at most
    /// `LIT_ITE_LEAVES` leaves): a value known to range over a small set.
    pub fn lit_ite(&self, t: Id) -> bool {
        fn leaves(t: &Terms, x: Id, budget: &mut i32) -> bool {
            match t.node(x) {
                N::Lit(..) => {
                    *budget -= 1;
                    *budget >= 0
                }
                N::Ite(_, p, q) => leaves(t, *p, budget) && leaves(t, *q, budget),
                _ => false,
            }
        }
        let mut b = LIT_ITE_LEAVES;
        matches!(self.node(t), N::Ite(..)) && leaves(self, t, &mut b)
    }

    pub fn select(&mut self, m: Id, a: Id) -> Id {
        if let Some(&r) = self.sel_cache.get(&(m, a)) {
            return r;
        }
        let r = self.select_uncached(m, a);
        self.sel_cache.insert((m, a), r);
        r
    }

    fn select_uncached(&mut self, m: Id, a: Id) -> Id {
        // an address ranging over a few literals: one select per literal
        if self.lit_ite(a)
            && let N::Ite(c, p, q) = self.node(a).clone()
        {
            let x = self.select(m, p);
            let y = self.select(m, q);
            return self.ite(c, x, y);
        }
        let mut cur = m;
        loop {
            match self.node(cur).clone() {
                N::Store(m2, b, v) => {
                    if a == b {
                        return v;
                    }
                    match (self.as_lit(a), self.as_lit(b)) {
                        (Some(x), Some(y)) if x != y => cur = m2,
                        (Some(_), None) if self.lit_ite(b) => {
                            // store at one of a few literal addresses
                            let c = self.eq(b, a);
                            let rest = self.select(m2, a);
                            return self.ite(c, v, rest);
                        }
                        _ => break,
                    }
                }
                N::ConstMem(byte, _) => return self.lit(byte as u64, 8),
                N::Ite(c, p, q) => {
                    let x = self.select(p, a);
                    let y = self.select(q, a);
                    return self.ite(c, x, y);
                }
                N::Copy(md, ms, d, s, n) => {
                    // a - d < n (unsigned) <=> d <= a < d + n
                    let off = self.bin(Bv2::Sub, a, d);
                    let inr = self.rel(Rel::Ult, off, n);
                    let sa = self.bin(Bv2::Add, off, s);
                    let x = self.select(ms, sa);
                    let y = self.select(md, a);
                    return self.ite(inr, x, y);
                }
                N::Fill(m, d, b, n) => {
                    let off = self.bin(Bv2::Sub, a, d);
                    let inr = self.rel(Rel::Ult, off, n);
                    let y = self.select(m, a);
                    return self.ite(inr, b, y);
                }
                _ => break,
            }
        }
        self.intern(N::Select(cur, a), Sort::Bv(8))
    }

    pub fn store(&mut self, m: Id, a: Id, v: Id) -> Id {
        // overwrite of the same literal address on top
        if let N::Store(m2, b, _) = self.node(m).clone()
            && a == b
        {
            return self.store(m2, a, v);
        }
        let s = self.sort(m);
        self.intern(N::Store(m, a, v), s)
    }

    pub fn copy(&mut self, md: Id, ms: Id, d: Id, s: Id, n: Id) -> Id {
        if self.as_lit(n) == Some(0) {
            return md;
        }
        let so = self.sort(md);
        self.intern(N::Copy(md, ms, d, s, n), so)
    }

    pub fn fill(&mut self, m: Id, d: Id, b: Id, n: Id) -> Id {
        if self.as_lit(n) == Some(0) {
            return m;
        }
        let so = self.sort(m);
        self.intern(N::Fill(m, d, b, n), so)
    }

    /// Little-endian load of `n` bytes at `a` (address width of the memory).
    pub fn load_le(&mut self, m: Id, a: Id, n: u32) -> Id {
        let aw = self.width(a);
        let mut acc = None;
        for k in 0..n {
            let off = self.lit(k as u64, aw);
            let ak = self.bin(Bv2::Add, a, off);
            let b = self.select(m, ak);
            acc = Some(match acc {
                None => b,
                Some(lo) => self.concat(b, lo),
            });
        }
        acc.expect("n > 0")
    }

    pub fn store_le(&mut self, m: Id, a: Id, v: Id, n: u32) -> Id {
        let aw = self.width(a);
        let mut cur = m;
        for k in 0..n {
            let off = self.lit(k as u64, aw);
            let ak = self.bin(Bv2::Add, a, off);
            let b = self.extract(8 * k + 7, 8 * k, v);
            cur = self.store(cur, ak, b);
        }
        cur
    }

    /// Whether `v` occurs in the DAG under `t`.
    pub fn occurs(&self, v: Id, t: Id) -> bool {
        self.topo(&[t]).contains(&v)
    }

    /// Substitute terms for terms (simultaneously) in `t`, re-simplifying.
    pub fn subst(&mut self, t: Id, map: &HashMap<Id, Id>) -> Id {
        let order = self.topo(&[t]);
        let mut m: HashMap<Id, Id> = map.clone();
        for x in order {
            if m.contains_key(&x) {
                continue;
            }
            let g = |y: &Id| *m.get(y).unwrap_or(y);
            let n = self.node(x).clone();
            let r = match n {
                N::Var(..) | N::Lit(..) | N::True | N::False | N::ConstMem(..) | N::HistNil => x,
                N::Not(a) => self.not(g(&a)),
                N::And(v) => {
                    let v: Vec<Id> = v.iter().map(g).collect();
                    self.and(&v)
                }
                N::Or(v) => {
                    let v: Vec<Id> = v.iter().map(g).collect();
                    self.or(&v)
                }
                N::Ite(a, b, c) => self.ite(g(&a), g(&b), g(&c)),
                N::Eq(a, b) => self.eq(g(&a), g(&b)),
                N::Bin(op, a, b) => self.bin(op, g(&a), g(&b)),
                N::Rel(r, a, b) => self.rel(r, g(&a), g(&b)),
                N::Extract(h, l, a) => self.extract(h, l, g(&a)),
                N::Zext(k, a) => self.zext(k, g(&a)),
                N::Sext(k, a) => self.sext(k, g(&a)),
                N::Concat(a, b) => self.concat(g(&a), g(&b)),
                N::Select(a, b) => self.select(g(&a), g(&b)),
                N::Store(a, b, c) => self.store(g(&a), g(&b), g(&c)),
                N::Copy(a, b, c, d, e) => self.copy(g(&a), g(&b), g(&c), g(&d), g(&e)),
                N::Fill(a, b, c, d) => self.fill(g(&a), g(&b), g(&c), g(&d)),
                N::App(f, v, so) => {
                    let v: Vec<Id> = v.iter().map(g).collect();
                    self.app(&f, v, so)
                }
                N::HistCons(i, v, p) => {
                    let v: Vec<Id> = v.iter().map(g).collect();
                    let p = g(&p);
                    self.hist_cons(i, &v, p)
                }
                N::Raw(text, b, so) => {
                    let b: Vec<(String, Id)> = b.iter().map(|(n, y)| (n.clone(), g(y))).collect();
                    self.raw_let(&text, b, so)
                }
            };
            m.insert(x, r);
        }
        m[&t]
    }

    pub fn app(&mut self, f: &str, args: Vec<Id>, s: Sort) -> Id {
        self.intern(N::App(f.to_string(), args, s), s)
    }

    pub fn hist_nil(&mut self) -> Id {
        self.intern(N::HistNil, Sort::Hist)
    }

    pub fn hist_cons(&mut self, imp: u32, args: &[Id], prev: Id) -> Id {
        let mut a = Vec::with_capacity(HIST_ARGS);
        for &x in args.iter().take(HIST_ARGS) {
            let w = self.width(x);
            a.push(self.zext(64 - w, x));
        }
        while a.len() < HIST_ARGS {
            a.push(self.lit(0, 64));
        }
        self.intern(N::HistCons(imp, a, prev), Sort::Hist)
    }

    /// Count leading zeros as an `ite` chain.
    pub fn clz(&mut self, a: Id) -> Id {
        let w = self.width(a);
        let mut r = self.lit(w as u64, w);
        for i in 0..w {
            let bit = self.extract(i, i, a);
            let one = self.lit(1, 1);
            let c = self.eq(bit, one);
            let v = self.lit((w - 1 - i) as u64, w);
            r = self.ite(c, v, r);
        }
        r
    }

    pub fn ctz(&mut self, a: Id) -> Id {
        let w = self.width(a);
        let mut r = self.lit(w as u64, w);
        for i in (0..w).rev() {
            let bit = self.extract(i, i, a);
            let one = self.lit(1, 1);
            let c = self.eq(bit, one);
            let v = self.lit(i as u64, w);
            r = self.ite(c, v, r);
        }
        r
    }

    pub fn popcnt(&mut self, a: Id) -> Id {
        let w = self.width(a);
        let mut r = self.lit(0, w);
        for i in 0..w {
            let bit = self.extract(i, i, a);
            let z = self.zext(w - 1, bit);
            r = self.bin(Bv2::Add, r, z);
        }
        r
    }

    fn children(&self, t: Id) -> Vec<Id> {
        match self.node(t) {
            N::Raw(_, b, _) => b.iter().map(|x| x.1).collect(),
            N::Var(..) | N::Lit(..) | N::True | N::False | N::ConstMem(..) | N::HistNil => {
                vec![]
            }
            N::Not(a) | N::Extract(_, _, a) | N::Zext(_, a) | N::Sext(_, a) => vec![*a],
            N::And(v) | N::Or(v) => v.clone(),
            N::Ite(a, b, c) | N::Store(a, b, c) => vec![*a, *b, *c],
            N::Copy(a, b, c, d, e) => vec![*a, *b, *c, *d, *e],
            N::Fill(a, b, c, d) => vec![*a, *b, *c, *d],
            N::Eq(a, b) | N::Bin(_, a, b) | N::Rel(_, a, b) | N::Concat(a, b) | N::Select(a, b) => {
                vec![*a, *b]
            }
            N::App(_, v, _) => v.clone(),
            N::HistCons(_, v, p) => {
                let mut v = v.clone();
                v.push(*p);
                v
            }
        }
    }

    /// Post-order of the DAG under `roots` (children first).
    pub fn topo(&self, roots: &[Id]) -> Vec<Id> {
        let mut seen = vec![false; self.nodes.len()];
        let mut out = Vec::new();
        let mut stack: Vec<(Id, bool)> = roots.iter().rev().map(|&r| (r, false)).collect();
        while let Some((t, done)) = stack.pop() {
            if done {
                out.push(t);
                continue;
            }
            if seen[t as usize] {
                continue;
            }
            seen[t as usize] = true;
            stack.push((t, true));
            for c in self.children(t).into_iter().rev() {
                if !seen[c as usize] {
                    stack.push((c, false));
                }
            }
        }
        out
    }

    /// Size of the DAG under `roots`.
    pub fn dag_size(&self, roots: &[Id]) -> usize {
        self.topo(roots).len()
    }

    fn atom(&self, t: Id, names: &HashMap<Id, String>) -> String {
        if let Some(n) = names.get(&t) {
            return n.clone();
        }
        self.expr(t, names)
    }

    /// The SMT-LIB text of node `t`, children by name when named.
    fn expr(&self, t: Id, names: &HashMap<Id, String>) -> String {
        let a = |x: &Id| self.atom(*x, names);
        match self.node(t) {
            N::Var(n, _) => quote(n),
            N::Lit(v, w) => {
                if w % 4 == 0 {
                    format!("#x{:0width$x}", v, width = (*w / 4) as usize)
                } else {
                    format!("#b{:0width$b}", v, width = *w as usize)
                }
            }
            N::True => "true".into(),
            N::False => "false".into(),
            N::Not(x) => format!("(not {})", a(x)),
            N::And(v) => format!("(and {})", v.iter().map(a).collect::<Vec<_>>().join(" ")),
            N::Or(v) => format!("(or {})", v.iter().map(a).collect::<Vec<_>>().join(" ")),
            N::Ite(c, x, y) => format!("(ite {} {} {})", a(c), a(x), a(y)),
            N::Eq(x, y) => format!("(= {} {})", a(x), a(y)),
            N::Bin(op, x, y) => format!("({} {} {})", op.smt(), a(x), a(y)),
            N::Rel(r, x, y) => {
                let o = match r {
                    Rel::Ult => "bvult",
                    Rel::Ule => "bvule",
                    Rel::Slt => "bvslt",
                    Rel::Sle => "bvsle",
                };
                format!("({o} {} {})", a(x), a(y))
            }
            N::Extract(h, l, x) => format!("((_ extract {h} {l}) {})", a(x)),
            N::Zext(n, x) => format!("((_ zero_extend {n}) {})", a(x)),
            N::Sext(n, x) => format!("((_ sign_extend {n}) {})", a(x)),
            N::Concat(x, y) => format!("(concat {} {})", a(x), a(y)),
            N::ConstMem(b, aw) => {
                format!("((as const (Array (_ BitVec {aw}) (_ BitVec 8))) #x{b:02x})")
            }
            N::Select(m, x) => format!("(select {} {})", a(m), a(x)),
            N::Store(m, x, v) => format!("(store {} {} {})", a(m), a(x), a(v)),
            N::Copy(md, ms, d, s, n) => format!(
                "(lambda ((i!c (_ BitVec 32))) (ite (bvult (bvsub i!c {d}) {n}) (select {ms} (bvadd (bvsub i!c {d}) {s})) (select {md} i!c)))",
                md = a(md),
                ms = a(ms),
                d = a(d),
                s = a(s),
                n = a(n)
            ),
            N::Fill(m, d, b, n) => format!(
                "(lambda ((i!c (_ BitVec 32))) (ite (bvult (bvsub i!c {d}) {n}) {b} (select {m} i!c)))",
                m = a(m),
                d = a(d),
                b = a(b),
                n = a(n)
            ),
            N::App(f, v, _) => {
                if v.is_empty() {
                    quote(f)
                } else {
                    format!(
                        "({} {})",
                        quote(f),
                        v.iter().map(a).collect::<Vec<_>>().join(" ")
                    )
                }
            }
            N::HistNil => "hnil".into(),
            N::HistCons(i, v, p) => format!(
                "(hcons #x{i:04x} {} {})",
                v.iter().map(a).collect::<Vec<_>>().join(" "),
                a(p)
            ),
            N::Raw(s, b, _) => {
                if b.is_empty() {
                    s.clone()
                } else {
                    let bs: Vec<String> = b
                        .iter()
                        .map(|(n, t)| format!("({} {})", quote(n), a(t)))
                        .collect();
                    format!("(let ({}) {s})", bs.join(" "))
                }
            }
        }
    }

    /// SMT-LIB declarations and definitions for everything under `roots`:
    /// variables are declared, interior nodes with more than one use become
    /// `define-fun`s. Returns the declarations, the definitions and the names
    /// of the roots.
    pub fn emit(&self, roots: &[Id]) -> (String, String, Vec<String>) {
        let order = self.topo(roots);
        let mut uses: HashMap<Id, u32> = HashMap::new();
        for &t in &order {
            for c in self.children(t) {
                *uses.entry(c).or_default() += 1;
            }
        }
        for &r in roots {
            *uses.entry(r).or_default() += 2;
        }
        let mut s = String::new();
        let mut d = String::new();
        let mut names: HashMap<Id, String> = HashMap::new();
        let mut funs: Vec<String> = Vec::new();
        let mut hist = false;
        for &t in &order {
            match self.node(t) {
                N::Var(n, so) => {
                    writeln!(d, "(declare-const {} {})", quote(n), so.smt()).unwrap();
                    names.insert(t, quote(n));
                    if *so == Sort::Hist {
                        hist = true;
                    }
                }
                N::App(f, args, so) => {
                    if !funs.contains(f) {
                        funs.push(f.clone());
                        let ps: Vec<String> = args.iter().map(|&x| self.sort(x).smt()).collect();
                        writeln!(
                            d,
                            "(declare-fun {} ({}) {})",
                            quote(f),
                            ps.join(" "),
                            so.smt()
                        )
                        .unwrap();
                    }
                    if args.iter().any(|&x| self.sort(x) == Sort::Hist) || *so == Sort::Hist {
                        hist = true;
                    }
                    if !args.is_empty() && uses.get(&t).copied().unwrap_or(0) > 1 {
                        let n = format!("t{t}");
                        writeln!(
                            s,
                            "(define-fun {n} () {} {})",
                            so.smt(),
                            self.expr(t, &names)
                        )
                        .unwrap();
                        names.insert(t, n);
                    }
                }
                N::Lit(..) | N::True | N::False | N::HistNil => {
                    if matches!(self.node(t), N::HistNil) {
                        hist = true;
                    }
                }
                _ => {
                    if matches!(self.node(t), N::HistCons(..)) {
                        hist = true;
                    }
                    if uses.get(&t).copied().unwrap_or(0) > 1 {
                        let n = format!("t{t}");
                        writeln!(
                            s,
                            "(define-fun {n} () {} {})",
                            self.sort(t).smt(),
                            self.expr(t, &names)
                        )
                        .unwrap();
                        names.insert(t, n);
                    }
                }
            }
        }
        let mut pre = String::new();
        if hist {
            let fields: Vec<String> = (0..HIST_ARGS)
                .map(|k| format!("(ha{k} (_ BitVec 64))"))
                .collect();
            writeln!(
                pre,
                "(declare-datatypes ((Hist 0)) (((hnil) (hcons (himp (_ BitVec 16)) {} (hprev Hist)))))",
                fields.join(" ")
            )
            .unwrap();
        }
        pre.push_str(&d);
        let rn = roots.iter().map(|&r| self.atom(r, &names)).collect();
        (pre, s, rn)
    }
}

/// Quote an SMT-LIB symbol when it is not simple.
pub fn quote(n: &str) -> String {
    let simple = !n.is_empty()
        && !n.chars().next().unwrap().is_ascii_digit()
        && n.chars()
            .all(|c| c.is_ascii_alphanumeric() || "~!@$%^&*_-+=<>.?/".contains(c));
    if simple {
        n.to_string()
    } else {
        format!("|{n}|")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn folds_flags_and_dispatch() {
        let mut t = Terms::new();
        let x = t.var("x", Sort::Bv(64));
        let y = t.var("y", Sort::Bv(64));
        let c = t.rel(Rel::Ult, x, y);
        let one = t.lit(1, 32);
        let zero = t.lit(0, 32);
        let flag = t.ite(c, one, zero);
        // br_if flag  ==>  flag != 0  ==>  c
        let nz = t.ne(flag, zero);
        assert_eq!(nz, c);
        let k = t.lit(5, 32);
        let five = t.lit(5, 32);
        assert_eq!(t.eq(k, five), t.tt());
        // shr then mask = extract
        let k3 = t.lit(3, 64);
        let sh = t.bin(Bv2::Lshr, x, k3);
        let m = t.lit(0xff, 64);
        let b = t.bin(Bv2::And, sh, m);
        let e = t.extract(10, 3, x);
        let z = t.zext(56, e);
        assert_eq!(b, z);
    }

    #[test]
    fn memory_reads_through_stores() {
        let mut t = Terms::new();
        let m0 = t.var("m", Sort::Mem(32));
        let a = t.lit(100, 32);
        let v = t.var("v", Sort::Bv(64));
        let m1 = t.store_le(m0, a, v, 8);
        let r = t.load_le(m1, a, 8);
        assert_eq!(r, v);
        let b = t.lit(200, 32);
        let r2 = t.select(m1, b);
        assert!(matches!(t.node(r2), N::Select(mm, _) if *mm == m0));
    }
}
