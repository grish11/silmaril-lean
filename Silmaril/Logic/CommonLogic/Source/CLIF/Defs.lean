module

public import Silmaril.Logic.CommonLogic.Source.Thms
public import Silmaril.Logic.Smt.SExpr.Defs

@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source.CLIF
open Silmaril.Logic.Smt

/-- The unquoted ASCII word class of the pinned Hets CLIF lexer.
Quotes, enclosing-name syntax and other CLIF lexical forms are not admitted. -/
def letter (n : Nat) : Bool :=
  n ≥ 33 && n ≤ 126 && ((n ≤ 38 && n != 34) || (n ≥ 42 && n != 64 && n != 92))

def marker (s : String) : Bool :=
  match s.toList with
  | '.'::'.'::'.'::_::_ => true
  | _ => false

def name (s : String) : Bool := !s.isEmpty && !marker s &&
  s.toList.all (fun c => letter c.toNat) &&
  !["=", "and", "or", "not", "if", "iff", "forall", "exists", "that", "...",
    "cl-text", "cl:text", "cl-imports", "cl:imports", "cl-module", "cl:module",
    "cl-excludes", "cl:excludes", "cl-comment", "cl:comment", "cl-prefix", "cl:prefix", "cl-roleset", "roleset:"].contains s

/-- CLIF plain words differ from SMT tokens: semicolon is a word character,
not a line comment. The shared structural stack builder contains no SMT semantics. -/
def lex : List UInt8 → List Char → List Tok → Option (List Tok)
  | [], cur, acc => some (flush cur acc).reverse
  | b::bs, cur, acc =>
      let n := b.toNat
      if n == 40 then lex bs [] (.lp :: flush cur acc)
      else if n == 41 then lex bs [] (.rp :: flush cur acc)
      else if n == 32 || n == 9 || n == 10 || n == 13 then lex bs [] (flush cur acc)
      else if letter n then lex bs (Char.ofNat n :: cur) acc
      else none

def forms (source : String) : Option (List SE) := do
  build (← lex source.toUTF8.data.toList [] []) [[]]

mutual
  def term : Nat → SE → Option (Source.Expr .individual)
    | 0, _ => none
    | _+1, .atom s => if name s then some (.individual s) else none
    | n+1, .list (h::ts) => do pure (.app (← head n h) (← arguments n ts))
    | _, _ => none
  def head : Nat → SE → Option (Source.Expr .reference)
    | 0, _ => none
    | _+1, .atom s => if name s then some (.reference s) else none
    | n+1, e@(.list _) => (term n e).map Source.Expr.lift
  def arguments : Nat → List SE → Option (Source.Expr .sequence)
    | 0, _ => none
    | _+1, [] => some .nil
    | n+1, .atom s :: rest =>
        if marker s then do pure (.append (.sequence s) (← arguments n rest))
        else do pure (.cons (← term n (.atom s)) (← arguments n rest))
    | n+1, e::rest => do pure (.cons (← term n e) (← arguments n rest))
end

/-- Mixed quantifier lists introduce independent individual/sequence binders,
from left to right. Nested lexical shadowing uses the innermost occurrence. -/
def quantify (universal : Bool) : List SE → Source.Formula → Option Source.Formula
  | [], body => some body
  | .atom s :: rest, body => do
      let inner ← quantify universal rest body
      if marker s then pure (if universal then .allSeq s inner else .exSeq s inner)
      else if name s then pure (if universal then .all s inner else .ex s inner)
      else none
  | _, _ => none

def sentence : Nat → SE → Option Source.Formula
  | 0, _ => none
  | n+1, .list [.atom "=",t,u] => do pure (.equal (← term n t) (← term n u))
  | n+1, .list (.atom "and"::ps) => do
      pure ((← ps.mapM (sentence n)).foldr Source.Formula.conj .tt)
  | n+1, .list (.atom "or"::ps) => do
      pure ((← ps.mapM (sentence n)).foldr Source.Formula.disj .ff)
  | n+1, .list [.atom "not",p] => (sentence n p).map Source.Formula.neg
  | n+1, .list [.atom "if",p,q] => do pure (.impl (← sentence n p) (← sentence n q))
  | n+1, .list [.atom "iff",p,q] => do pure (.iff (← sentence n p) (← sentence n q))
  | n+1, .list [.atom "forall",.list bound,p] => do quantify true bound (← sentence n p)
  | n+1, .list [.atom "exists",.list bound,p] => do quantify false bound (← sentence n p)
  | n+1, .list (h::ts) => do pure (.pred (← head n h) (← arguments n ts))
  | _, _ => none

/-- One complete text, optionally named by cl-text/cl:text; imports/modules,
comments, restricted binders and quotation are outside this Core profile. -/
def read (fuel : Nat) (source : String) : Option (List Source.Formula) := do
  match ← forms source with
  | [.list (.atom "cl-text" :: .atom textName :: body)]
  | [.list (.atom "cl:text" :: .atom textName :: body)] =>
      if name textName then body.mapM (sentence fuel) else none
  | [] => none
  | body => body.mapM (sentence fuel)

/-- The exact text, all sentences and all successful typed elaborations stay bound. -/
structure Text {S : Core.Signature} (names : Names S) where
  declarations_valid : names.Valid
  source : String
  fuel : Nat
  raw : List Source.Formula
  typed : List (Core.Sentence S)
  parsed : read fuel source = some raw
  elaborated : raw.mapM (Source.Formula.elaborate names [] []) = some typed

end Silmaril.Logic.CommonLogic.Source.CLIF
