module

public import Silmaril.Courses.Cambridge.AstCodec
public import Silmaril.Courses.Cambridge.L2.Syntax

/-! Structural codecs for named L2 terms and expression types. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.Codec

open Silmaril.Courses.Cambridge.AstCodec

def typeTree : Ty → Tree
  | .int => node "type-int" []
  | .bool => node "type-bool" []
  | .unit => node "type-unit" []
  | .arr domain codomain => node "type-arrow" [typeTree domain, typeTree codomain]

def termTree : RawExpr → Tree
  | .int n => node "int" [.atom n.repr]
  | .bool b => node "bool" [.atom (boolName b)]
  | .binary left op right => node "binary" [termTree left, .atom (opName op), termTree right]
  | .cond test yes no => node "if" [termTree test, termTree yes, termTree no]
  | .assign loc value => node "assign" [.atom loc, termTree value]
  | .deref loc => node "deref" [.atom loc]
  | .skip => node "skip" []
  | .seq left right => node "seq" [termTree left, termTree right]
  | .loop test body => node "while" [termTree test, termTree body]
  | .var name => node "var" [.atom name]
  | .lam name domain body => node "lambda" [.atom name, typeTree domain, termTree body]
  | .app fn arg => node "apply" [termTree fn, termTree arg]
  | .letE name type value body =>
      node "let" [.atom name, typeTree type, termTree value, termTree body]
  | .letRecFun fn param domain codomain fnBody body =>
      node "let-rec" [.atom fn, .atom param, typeTree domain, typeTree codomain,
        termTree fnBody, termTree body]

def readNamedFields (tag : String) (fields : List (Datum Ty RawExpr)) :
    Option (Datum Ty RawExpr) :=
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
  | "var" => match fields with
    | [.atom name] => some (.term (.var name))
    | _ => none
  | "lambda" => match fields with
    | [.atom name, .type domain, .term body] => some (.term (.lam name domain body))
    | _ => none
  | "apply" => match fields with
    | [.term fn, .term arg] => some (.term (.app fn arg))
    | _ => none
  | "let" => match fields with
    | [.atom name, .type type, .term value, .term body] =>
        some (.term (.letE name type value body))
    | _ => none
  | "let-rec" => match fields with
    | [.atom fn, .atom param, .type domain, .type codomain, .term fnBody, .term body] =>
        some (.term (.letRecFun fn param domain codomain fnBody body))
    | _ => none
  | _ => none

/-- Share expression type decoding across the named and resolved term schemas. -/
def readWithTypes {Term : Type}
    (readTermFields : String → List (Datum Ty Term) → Option (Datum Ty Term))
    (tag : String) (fields : List (Datum Ty Term)) : Option (Datum Ty Term) :=
  match tag with
  | "type-int" => match fields with
    | [] => some (.type .int)
    | _ => none
  | "type-bool" => match fields with
    | [] => some (.type .bool)
    | _ => none
  | "type-unit" => match fields with
    | [] => some (.type .unit)
    | _ => none
  | "type-arrow" => match fields with
    | [.type dom, .type cod] => some (.type (.arr dom cod))
    | _ => none
  | _ => readTermFields tag fields

def readFields := readWithTypes readNamedFields

def readNode := taggedReader readFields

theorem read_typeTree {Term : Type}
    (readTermFields : String → List (Datum Ty Term) → Option (Datum Ty Term)) (type : Ty) :
    readTree (taggedReader (readWithTypes readTermFields)) (typeTree type) = some (.type type) := by
  induction type <;> simp [typeTree, taggedReader, readWithTypes, *]

private theorem read_termTree (term : RawExpr) :
    readTree readNode (termTree term) = some (.term term) := by
  unfold readNode readFields
  induction term <;> simp [termTree, taggedReader, readWithTypes, readNamedFields,
      read_typeTree, *]

def termSExp : AstCodec.Codec RawExpr :=
  versioned "L2" "term" ⟨termTree, (fun t => readTree readNode t >>= Datum.getTerm),
    by intro term; rw [read_termTree]; rfl⟩

def typeSExp : AstCodec.Codec Ty :=
  versioned "L2" "type" ⟨typeTree, (fun t => readTree readNode t >>= Datum.getType),
    by intro type; rw [readNode, readFields, read_typeTree]; rfl⟩

def termJson := asJson termSExp
def typeJson := asJson typeSExp

end Silmaril.Courses.Cambridge.L2.Codec
