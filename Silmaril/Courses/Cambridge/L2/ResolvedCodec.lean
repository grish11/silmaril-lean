module

public import Silmaril.Courses.Cambridge.L2.Codec

/-! Structural codecs for resolved L2 terms. Bound indices are preserved as
syntax data, including indices outside the enclosing binder depth. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.ResolvedCodec

open Silmaril.Courses.Cambridge.AstCodec
open L2.Codec (typeTree)

def termTree : Expr → Tree
  | .int n => node "int" [.atom n.repr]
  | .bool b => node "bool" [.atom (boolName b)]
  | .binary left op right => node "binary" [termTree left, .atom (opName op), termTree right]
  | .cond test yes no => node "if" [termTree test, termTree yes, termTree no]
  | .assign loc value => node "assign" [.atom loc, termTree value]
  | .deref loc => node "deref" [.atom loc]
  | .skip => node "skip" []
  | .seq left right => node "seq" [termTree left, termTree right]
  | .loop test body => node "while" [termTree test, termTree body]
  | .bvar index => node "bvar" [.atom index.repr]
  | .fvar name => node "fvar" [.atom name]
  | .lam domain body => node "lambda" [typeTree domain, termTree body]
  | .app fn arg => node "apply" [termTree fn, termTree arg]
  | .letE type value body =>
      node "let" [typeTree type, termTree value, termTree body]
  | .letRecFun domain codomain fnBody body =>
      node "let-rec" [typeTree domain, typeTree codomain, termTree fnBody, termTree body]

def readTermFields (tag : String) (fields : List (Datum Ty Expr)) :
    Option (Datum Ty Expr) :=
  match tag with
  | "int" => match fields with
    | [.atom n] => (readInt n).map fun n => .term (.int n)
    | _ => none
  | "bool" => match fields with
    | [.atom b] => (readBool b).map fun b => .term (.bool b)
    | _ => none
  | "binary" => match fields with
    | [.term left, .atom op, .term right] =>
        (readOp op).map fun op => .term (.binary left op right)
    | _ => none
  | "if" => match fields with
    | [.term test, .term yes, .term no] => some (.term (.cond test yes no))
    | _ => none
  | "assign" => match fields with
    | [.atom loc, .term value] => some (.term (.assign loc value))
    | _ => none
  | "deref" => match fields with
    | [.atom loc] => some (.term (.deref loc))
    | _ => none
  | "skip" => match fields with
    | [] => some (.term .skip)
    | _ => none
  | "seq" => match fields with
    | [.term left, .term right] => some (.term (.seq left right))
    | _ => none
  | "while" => match fields with
    | [.term test, .term body] => some (.term (.loop test body))
    | _ => none
  | "bvar" => match fields with
    | [.atom index] => (readNat index).map fun n => .term (.bvar n)
    | _ => none
  | "fvar" => match fields with
    | [.atom name] => some (.term (.fvar name))
    | _ => none
  | "lambda" => match fields with
    | [.type domain, .term body] => some (.term (.lam domain body))
    | _ => none
  | "apply" => match fields with
    | [.term fn, .term arg] => some (.term (.app fn arg))
    | _ => none
  | "let" => match fields with
    | [.type type, .term value, .term body] => some (.term (.letE type value body))
    | _ => none
  | "let-rec" => match fields with
    | [.type domain, .type codomain, .term fnBody, .term body] =>
        some (.term (.letRecFun domain codomain fnBody body))
    | _ => none
  | _ => none

def readNode := taggedReader (L2.Codec.readWithTypes readTermFields)

private theorem read_termTree (term : Expr) :
    readTree readNode (termTree term) = some (.term term) := by
  unfold readNode
  induction term <;> simp [termTree, taggedReader, L2.Codec.readWithTypes,
      readTermFields, L2.Codec.read_typeTree, *]

def termSExp : AstCodec.Codec Expr :=
  versioned "L2" "resolved-term" ⟨termTree, (fun tree => readTree readNode tree >>= Datum.getTerm),
    by intro term; rw [read_termTree]; rfl⟩

def termJson := asJson termSExp

end Silmaril.Courses.Cambridge.L2.ResolvedCodec
