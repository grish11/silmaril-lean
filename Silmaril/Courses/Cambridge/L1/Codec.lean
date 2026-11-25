module

public import Silmaril.Courses.Cambridge.AstCodec
public import Silmaril.Courses.Cambridge.L1.Typing

/-! Structural codecs for L1 terms and expression types. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.Codec

open Silmaril.Courses.Cambridge.AstCodec

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

def typeTree : Ty → Tree
  | .int => node "type-int" []
  | .bool => node "type-bool" []
  | .unit => node "type-unit" []

def readFields (tag : String) (fields : List (Datum Ty Expr)) :
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
  | "type-int" => match fields with
    | [] => some (.type .int)
    | _ => none
  | "type-bool" => match fields with
    | [] => some (.type .bool)
    | _ => none
  | "type-unit" => match fields with
    | [] => some (.type .unit)
    | _ => none
  | _ => none

def readNode : List (Datum Ty Expr) → Option (Datum Ty Expr)
  | .atom tag :: fields => readFields tag fields
  | _ => none


private theorem read_termTree (term : Expr) :
    readTree readNode (termTree term) = some (.term term) := by
  induction term <;> simp [termTree, readNode, readFields, *]

private theorem read_typeTree (type : Ty) :
    readTree readNode (typeTree type) = some (.type type) := by
  cases type <;> simp [typeTree, readNode, readFields]

def termSExp : AstCodec.Codec Expr :=
  versioned "L1" "term" ⟨termTree, (fun t => readTree readNode t >>= Datum.getTerm),
    by intro term; rw [read_termTree]; rfl⟩

def typeSExp : AstCodec.Codec Ty :=
  versioned "L1" "type" ⟨typeTree, (fun t => readTree readNode t >>= Datum.getType),
    by intro type; rw [read_typeTree]; rfl⟩

def termJson := asJson termSExp
def typeJson := asJson typeSExp

end Silmaril.Courses.Cambridge.L1.Codec
