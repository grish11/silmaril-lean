module

public import Silmaril.Courses.Cambridge.L3.Codec

/-! Structural codecs for resolved L3 terms. Bound indices are preserved as
syntax data, including indices outside the enclosing binder depth. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.ResolvedCodec

open Silmaril.Courses.Cambridge.AstCodec
open L3.Codec (typeTree)

def termTree : Expr → Tree
  | .int n => node "int" [.atom n.repr]
  | .bool b => node "bool" [.atom (boolName b)]
  | .binary left op right => node "binary" [termTree left, .atom (opName op), termTree right]
  | .cond test yes no => node "if" [termTree test, termTree yes, termTree no]
  | .assign left right => node "assign" [termTree left, termTree right]
  | .deref reference => node "deref" [termTree reference]
  | .ref value => node "ref" [termTree value]
  | .loc address => node "loc" [.atom address.repr]
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
  | .pair left right => node "pair" [termTree left, termTree right]
  | .fst pair => node "fst" [termTree pair]
  | .snd pair => node "snd" [termTree pair]
  | .inl payload type => node "inl" [termTree payload, typeTree type]
  | .inr payload type => node "inr" [termTree payload, typeTree type]
  | .matchSum scrutinee leftType left rightType right =>
      node "match-sum" [termTree scrutinee, typeTree leftType, termTree left,
        typeTree rightType, termTree right]
  | .record labels fields =>
      node "record" (List.ofFn fun i => node "field" [.atom (labels.label i), termTree (fields i)])
  | .project record label => node "project" [termTree record, .atom label]

def asTermField : Datum Ty Expr → Option (Label × Expr)
  | .termField name value => some (name, value)
  | _ => none

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
    | [.term left, .term right] => some (.term (.assign left right))
    | _ => none
  | "deref" => match fields with
    | [.term value] => some (.term (.deref value))
    | _ => none
  | "ref" => match fields with
    | [.term value] => some (.term (.ref value))
    | _ => none
  | "loc" => match fields with
    | [.atom address] => (readNat address).map fun n => .term (.loc n)
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
  | "pair" => match fields with
    | [.term left, .term right] => some (.term (.pair left right))
    | _ => none
  | "fst" => match fields with
    | [.term pair] => some (.term (.fst pair))
    | _ => none
  | "snd" => match fields with
    | [.term pair] => some (.term (.snd pair))
    | _ => none
  | "inl" => match fields with
    | [.term payload, .type type] => some (.term (.inl payload type))
    | _ => none
  | "inr" => match fields with
    | [.term payload, .type type] => some (.term (.inr payload type))
    | _ => none
  | "match-sum" => match fields with
    | [.term scrutinee, .type leftType, .term left, .type rightType, .term right] =>
        some (.term (.matchSum scrutinee leftType left rightType right))
    | _ => none
  | "field" => match fields with
    | [.atom label, .term term] => some (.termField label term)
    | _ => none
  | "record" => do
      let entries ← fields.mapM asTermField
      let ⟨labels, values⟩ ← RecordLabels.ofEntries entries
      return .term (.record labels values)
  | "project" => match fields with
    | [.term record, .atom label] => some (.term (.project record label))
    | _ => none
  | _ => none

def readNode := taggedReader (L3.Codec.readWithTypes readTermFields)

private theorem read_termTree (term : Expr) :
    readTree readNode (termTree term) = some (.term term) := by
  unfold readNode
  induction term with
  | record labels fields ih =>
    rw [termTree, readTree_node, mapM_ofFn_some _ _ (fun i => .termField (labels.label i) (fields i))
      (fun i => by simp [taggedReader, L3.Codec.readWithTypes, readTermFields, ih i])]
    simp [taggedReader, L3.Codec.readWithTypes, readTermFields]
    rw [mapM_ofFn_some (fun i => Datum.termField (labels.label i) (fields i))
      asTermField (fun i => (labels.label i, fields i)) (fun _ => rfl)]
    change (RecordLabels.ofEntries (labels.entries fields)).bind _ = _
    simp
  | _ => simp [termTree, taggedReader, L3.Codec.readWithTypes,
      readTermFields, L3.Codec.read_typeTree, *]

def termSExp : AstCodec.Codec Expr :=
  versioned "L3" "resolved-term" ⟨termTree, (fun tree => readTree readNode tree >>= Datum.getTerm),
    by intro term; rw [read_termTree]; rfl⟩

def termJson := asJson termSExp

end Silmaril.Courses.Cambridge.L3.ResolvedCodec
