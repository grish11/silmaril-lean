module

public import Silmaril.Courses.Cambridge.AstCodec
public import Silmaril.Courses.Cambridge.L3.NamedSyntax
public import Silmaril.Courses.Cambridge.L3.RecordFields

/-! Structural codecs for named L3 terms and expression types. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Codec

open Silmaril.Courses.Cambridge.AstCodec

def typeTree : Ty → Tree
  | .int => node "type-int" []
  | .bool => node "type-bool" []
  | .unit => node "type-unit" []
  | .arr domain codomain => node "type-arrow" [typeTree domain, typeTree codomain]
  | .prod left right => node "type-product" [typeTree left, typeTree right]
  | .sum left right => node "type-sum" [typeTree left, typeTree right]
  | .ref contents => node "type-ref" [typeTree contents]
  | .record labels fields =>
      node "type-record" (List.ofFn fun i => node "type-field" [.atom (labels.label i), typeTree (fields i)])

def termTree : RawExpr → Tree
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
  | .var name => node "var" [.atom name]
  | .lam name domain body => node "lambda" [.atom name, typeTree domain, termTree body]
  | .app fn arg => node "apply" [termTree fn, termTree arg]
  | .letE name type value body =>
      node "let" [.atom name, typeTree type, termTree value, termTree body]
  | .letRecFun fn param domain codomain fnBody body =>
      node "let-rec" [.atom fn, .atom param, typeTree domain, typeTree codomain,
        termTree fnBody, termTree body]

  | .pair left right => node "pair" [termTree left, termTree right]
  | .fst pair => node "fst" [termTree pair]
  | .snd pair => node "snd" [termTree pair]
  | .inl payload type => node "inl" [termTree payload, typeTree type]
  | .inr payload type => node "inr" [termTree payload, typeTree type]
  | .matchSum scrutinee leftName leftType left rightName rightType right =>
      node "match-sum" [termTree scrutinee, .atom leftName, typeTree leftType, termTree left,
        .atom rightName, typeTree rightType, termTree right]
  | .record labels fields =>
      node "record" (List.ofFn fun i => node "field" [.atom (labels.label i), termTree (fields i)])
  | .project record label => node "project" [termTree record, .atom label]

def asTypeField {Term : Type} : Datum Ty Term → Option (Label × Ty)
  | .typeField name value => some (name, value)
  | _ => none

def asTermField : Datum Ty RawExpr → Option (Label × RawExpr)
  | .termField name value => some (name, value)
  | _ => none

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
    | [.term scrutinee, .atom leftName, .type leftType, .term left,
        .atom rightName, .type rightType, .term right] =>
        some (.term (.matchSum scrutinee leftName leftType left rightName rightType right))
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
  | "type-product" => match fields with
    | [.type left, .type right] => some (.type (.prod left right))
    | _ => none
  | "type-sum" => match fields with
    | [.type left, .type right] => some (.type (.sum left right))
    | _ => none
  | "type-ref" => match fields with
    | [.type contents] => some (.type (.ref contents))
    | _ => none
  | "type-field" => match fields with
    | [.atom label, .type type] => some (.typeField label type)
    | _ => none
  | "type-record" => do
      let entries ← fields.mapM asTypeField
      let ⟨labels, values⟩ ← RecordLabels.ofEntries entries
      return .type (.record labels values)
  | _ => readTermFields tag fields

def readFields := readWithTypes readNamedFields

def readNode := taggedReader readFields

theorem read_typeTree {Term : Type}
    (readTermFields : String → List (Datum Ty Term) → Option (Datum Ty Term)) (type : Ty) :
    readTree (taggedReader (readWithTypes readTermFields)) (typeTree type) = some (.type type) := by
  induction type with
  | record labels fields ih =>
    rw [typeTree, readTree_node, mapM_ofFn_some _ _ (fun i => .typeField (labels.label i) (fields i))
      (fun i => by simp [taggedReader, readWithTypes, ih i])]
    simp [taggedReader, readWithTypes]
    rw [mapM_ofFn_some (fun i => Datum.typeField (labels.label i) (fields i))
      asTypeField (fun i => (labels.label i, fields i)) (fun _ => rfl)]
    change (RecordLabels.ofEntries (labels.entries fields)).bind _ = _
    simp
  | _ => simp [typeTree, taggedReader, readWithTypes, *]

private theorem read_termTree (term : RawExpr) :
    readTree readNode (termTree term) = some (.term term) := by
  unfold readNode readFields
  induction term with
  | record labels fields ih =>
    rw [termTree, readTree_node, mapM_ofFn_some _ _ (fun i => .termField (labels.label i) (fields i))
      (fun i => by simp [taggedReader, readWithTypes, readNamedFields, ih i])]
    simp [taggedReader, readWithTypes, readNamedFields]
    rw [mapM_ofFn_some (fun i => Datum.termField (labels.label i) (fields i))
      asTermField (fun i => (labels.label i, fields i)) (fun _ => rfl)]
    change (RecordLabels.ofEntries (labels.entries fields)).bind _ = _
    simp
  | _ => simp [termTree, taggedReader, readWithTypes, readNamedFields,
      read_typeTree, *]

def termSExp : AstCodec.Codec RawExpr :=
  versioned "L3" "term" ⟨termTree, (fun t => readTree readNode t >>= Datum.getTerm),
    by intro term; rw [read_termTree]; rfl⟩

def typeSExp : AstCodec.Codec Ty :=
  versioned "L3" "type" ⟨typeTree, (fun t => readTree readNode t >>= Datum.getType),
    by intro type; rw [readNode, readFields, read_typeTree]; rfl⟩

def termJson := asJson termSExp
def typeJson := asJson typeSExp

end Silmaril.Courses.Cambridge.L3.Codec
