module

public import Silmaril.Formats.Csv.Defs
public import Silmaril.Semantics.Relational.Scan.Defs

/-! # Typed CSV with an explicit ordered nullable schema

The first lexical row is the header. In a positive-width table, `N` is null and
`T` followed by the caller's text is a present value. A zero-column schema uses
one empty field as its header and as each body row, preserving the row count.
-/

@[expose] public section

namespace Silmaril.Formats.Csv.Typed

open Silmaril.Relational

/-- Ordered `(header field, kind)` labels supplied out of band. -/
abbrev Schema (Kind : Type*) := Scan.Schema Field Kind

abbrev Table {Kind : Type*} (schema : Schema Kind) (Value : Kind → Type*) :=
  Scan.Table schema Value

/-- The caller's partial conversions for present cells, before nullable tagging. -/
structure CellCodec (α : Type*) where
  print : α → Option Field
  parse : Field → Option α

/-- Parsing each successfully printed value's text recovers the value. -/
def CellCodec.ParsePrint {α : Type*} (codec : CellCodec α) : Prop :=
  ∀ {value text}, codec.print value = some text → codec.parse text = some value

/-- Printing each successfully parsed value recovers the exact input text. -/
def CellCodec.PrintParse {α : Type*} (codec : CellCodec α) : Prop :=
  ∀ {value text}, codec.parse text = some value → codec.print value = some text

inductive Error where
  | missingHeader
  | headerMismatch
  | width (expected observed : Nat)
  | zeroColumnMarker
  | invalidTag (column : Nat)
  | printCell (column : Nat)
  | parseCell (column : Nat)
  | malformedWire
  | unrepresentableWire
  deriving DecidableEq, Repr

namespace Internal

def nullTag : UInt8 := 0x4E
def textTag : UInt8 := 0x54

def zeroColumnRow : Row := [[]]

/-- Traverse dependent positions from left to right, stopping at the first error. -/
def collect {E : Type*} : {n : Nat} → {α : Fin n → Type*} →
    ((i : Fin n) → Except E (α i)) → Except E ((i : Fin n) → α i)
  | 0, _, _ => .ok (fun i => i.elim0)
  | _ + 1, α, f => do
    let first ← f 0
    let rest ← collect (α := fun i => α i.succ) fun i => f i.succ
    pure (Fin.cases first rest)

def exportCell {α : Type*} (codec : CellCodec α) (column : Nat) : Option α → Except Error Field
  | none => .ok [nullTag]
  | some value =>
    match codec.print value with
    | none => .error (.printCell column)
    | some text => .ok (textTag :: text)

def importCell {α : Type*} (codec : CellCodec α) (column : Nat) (field : Field) :
    Except Error (Option α) :=
  if field = [nullTag] then .ok none else
    match field with
    | tag :: text =>
      if tag = textTag then
        match codec.parse text with
        | some value => .ok (some value)
        | none => .error (.parseCell column)
      else .error (.invalidTag column)
    | [] => .error (.invalidTag column)

end Internal

open Silmaril.Formats.Csv.Typed.Internal

variable {Kind : Type*} {Value : Kind → Type*}

/-- The expected first record, in schema order. -/
def header (schema : Schema Kind) : Row :=
  if schema.width = 0 then zeroColumnRow else List.ofFn (Prod.fst ∘ schema.kind)

namespace Internal

def exportRow (schema : Schema Kind) (codecs : (kind : Kind) → CellCodec (Value kind))
    (row : Scan.Row schema Value) : Except Error Row :=
  if schema.width = 0 then .ok zeroColumnRow else do
    let fields ← collect fun i => exportCell (codecs (schema.kind i).2) i.val (row i)
    pure (List.ofFn fields)

def importRow (schema : Schema Kind) (codecs : (kind : Kind) → CellCodec (Value kind))
    (row : Row) : Except Error (Scan.Row schema Value) :=
  if zero : schema.width = 0 then
    if row = zeroColumnRow then .ok (fun i => (i.cast zero).elim0) else .error .zeroColumnMarker
  else if shape : row.length = schema.width then
    collect fun i => importCell (codecs (schema.kind i).2) i.val (row.get (i.cast shape.symm))
  else .error (.width schema.width row.length)

end Internal

/-- Emit the explicit header and the ordered lexical body rows. -/
def exportRows (schema : Schema Kind) (codecs : (kind : Kind) → CellCodec (Value kind))
    (table : Table schema Value) : Except Error Rows := do
  let body ← table.mapM (exportRow schema codecs)
  pure (header schema :: body)

/-- Check the header, widths, nullable tags and caller text conversions. -/
def importRows (schema : Schema Kind) (codecs : (kind : Kind) → CellCodec (Value kind)) :
    Rows → Except Error (Table schema Value)
  | [] => .error .missingHeader
  | first :: body =>
    if first = header schema then body.mapM (importRow schema codecs) else .error .headerMismatch

/-- Export a typed table through the RFC 4180 ASCII writer. -/
def encode (schema : Schema Kind) (codecs : (kind : Kind) → CellCodec (Value kind))
    (table : Table schema Value) : Except Error Bytes := do
  let rows ← exportRows schema codecs table
  match Csv.encode rows with
  | some bytes => .ok bytes
  | none => .error .unrepresentableWire

/-- Decode the lexical CSV, then interpret the fields under the supplied schema. -/
def decode (schema : Schema Kind) (codecs : (kind : Kind) → CellCodec (Value kind))
    (bytes : Bytes) : Except Error (Table schema Value) :=
  match Csv.decode bytes with
  | some rows => importRows schema codecs rows
  | none => .error .malformedWire

end Silmaril.Formats.Csv.Typed
