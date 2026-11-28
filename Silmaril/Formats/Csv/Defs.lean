module

public import Silmaril.Prelude.Bytes.Format.Defs

/-! # RFC 4180 CSV over bytes

Rows contain one or more uninterpreted byte fields. The profile uses the ASCII
`TEXTDATA` and quoted-field productions from RFC 4180 §2, CRLF record separators,
and an optional final CRLF. The empty file denotes zero rows. A CRLF by itself
terminates a row containing one empty field. Row widths may differ, and commas
always separate fields, including an empty field after a final comma.
-/

@[expose] public section

namespace Silmaril.Formats.Csv

abbrev Bytes := List UInt8
abbrev Field := Bytes
abbrev Row := List Field
abbrev Rows := List Row

namespace Internal

def quote : UInt8 := 0x22
def comma : UInt8 := 0x2C
def cr : UInt8 := 0x0D
def lf : UInt8 := 0x0A

/-- The `TEXTDATA` character class from RFC 4180 §2. -/
def textData (b : UInt8) : Bool :=
  (0x20 ≤ b && b ≤ 0x21) || (0x23 ≤ b && b ≤ 0x2B) || (0x2D ≤ b && b ≤ 0x7E)

/-- Bytes other than quotes that may appear literally inside a quoted field. -/
def quotedData (b : UInt8) : Bool := textData b || b == comma || b == cr || b == lf

def fieldData (b : UInt8) : Bool := b == quote || quotedData b

/-- The byte alphabet for the shared delimiter scanner. The UTF-8 caller
    checks the actual encoding of each unescaped field. -/
inductive Alphabet where
  | ascii
  | utf8Bytes

def bareData : Alphabet → UInt8 → Bool
  | .ascii => textData
  | .utf8Bytes => fun b => textData b || decide (0x80 ≤ b)

def quotedDataFor (alphabet : Alphabet) (b : UInt8) : Bool :=
  bareData alphabet b || b == comma || b == cr || b == lf

def fieldDataFor (alphabet : Alphabet) (b : UInt8) : Bool := b == quote || quotedDataFor alphabet b

@[simp] theorem bareData_ascii : bareData .ascii = textData := rfl
@[simp] theorem quotedDataFor_ascii : quotedDataFor .ascii = quotedData := rfl
@[simp] theorem fieldDataFor_ascii : fieldDataFor .ascii = fieldData := rfl

/-- Double every quote in a field. -/
def escape : Field → Bytes
  | [] => []
  | b :: rest => if b = quote then quote :: quote :: escape rest else b :: escape rest

def quoteField (field : Field) : Bytes := quote :: escape field ++ [quote]

end Internal

open Internal

/-- Field contents and arities representable by the wire profile. -/
def WellFormed (rows : Rows) : Prop :=
  ∀ row ∈ rows, row ≠ [] ∧ ∀ field ∈ row, field.all fieldData = true

/-- The unquoted and quoted field productions. -/
inductive FieldWire : Bytes → Field → Prop where
  | bare {field : Field} (ok : field.all textData = true) : FieldWire field field
  | quoted {field : Field} (ok : field.all fieldData = true) : FieldWire (quoteField field) field

/-- A nonempty sequence of rows, with the first row given separately. The
    grammar builds from the first field and distinguishes commas, CRLF
    separators, and the optional last CRLF. -/
inductive Records : Bytes → Row → Rows → Prop where
  | last {wire : Bytes} {field : Field} : FieldWire wire field → Records wire [field] []
  | terminated {wire : Bytes} {field : Field} :
      FieldWire wire field → Records (wire ++ [cr, lf]) [field] []
  | moreFields {wire tail : Bytes} {field : Field} {row : Row} {rows : Rows} :
      FieldWire wire field → Records tail row rows →
      Records (wire ++ comma :: tail) (field :: row) rows
  | moreRows {wire tail : Bytes} {field : Field} {row : Row} {rows : Rows} :
      FieldWire wire field → tail ≠ [] → Records tail row rows →
      Records (wire ++ cr :: lf :: tail) [field] (row :: rows)

/-- The whole-file grammar with the empty-input convention. -/
inductive Parses : Bytes → Rows → Prop where
  | empty : Parses [] []
  | records {wire : Bytes} {row : Row} {rows : Rows} :
      wire ≠ [] → Records wire row rows → Parses wire (row :: rows)

/-- Reuse the byte-format interface for the wire relation. -/
def format : ByteFormat Rows := ⟨"csv-rfc4180-ascii", Parses⟩

namespace Internal

/-- The unconsumed suffix is no longer than the input. -/
structure ParsedField (input : Bytes) where
  field : Field
  rest : Bytes
  rest_le : rest.length ≤ input.length

/-- Read the contents and closing quote after the opening quote. -/
def readQuoted : (input : Bytes) → (alphabet : Alphabet := .ascii) → Option (ParsedField input)
  | [], _ => none
  | b :: bs, alphabet =>
    if b = quote then
      match bs with
      | [] => some ⟨[], [], by simp⟩
      | c :: cs =>
        if c = quote then (readQuoted cs alphabet).map fun p => ⟨quote :: p.field, p.rest, by
          have := p.rest_le
          simp only [List.length_cons]; omega⟩
        else some ⟨[], c :: cs, by simp⟩
    else if quotedDataFor alphabet b then (readQuoted bs alphabet).map fun p => ⟨b :: p.field, p.rest, by
      have := p.rest_le
      simp only [List.length_cons]; omega⟩
    else none

/-- Read a field candidate and leave its suffix for delimiter validation. -/
def readField (input : Bytes) (alphabet : Alphabet := .ascii) : Option (ParsedField input) :=
  match input with
  | [] => some ⟨[], [], Nat.le_refl _⟩
  | b :: bs =>
    if b = quote then (readQuoted bs alphabet).map fun p => ⟨p.field, p.rest, by
      exact Nat.le_trans p.rest_le (Nat.le_succ _)⟩
    else some ⟨(b :: bs).takeWhile (bareData alphabet), (b :: bs).dropWhile (bareData alphabet),
      (List.dropWhile_sublist (bareData alphabet)).length_le⟩

/-- Finish a row and the following rows. An empty input here is an empty field. -/
def readRecords (input : Bytes) (alphabet : Alphabet := .ascii) : Option (Row × Rows) := do
  let p ← readField input alphabet
  have _bound := p.rest_le
  match _h : p.rest with
  | [] => pure ([p.field], [])
  | b :: bs =>
    if b = comma then
      let (row, rows) ← readRecords bs alphabet
      pure (p.field :: row, rows)
    else if b = cr then
      match _hbs : bs with
      | c :: rest =>
        if c = lf then
          match _hr : rest with
          | [] => pure ([p.field], [])
          | d :: ds =>
            let (row, rows) ← readRecords (d :: ds) alphabet
            pure ([p.field], row :: rows)
        else none
      | [] => none
    else none
termination_by input.length
decreasing_by all_goals simp_all only [List.length_cons]; omega

def renderRow : Row → Bytes
  | [] => []
  | [field] => quoteField field ++ [cr, lf]
  | field :: next :: rest => quoteField field ++ comma :: renderRow (next :: rest)

def render (rows : Rows) : Bytes := rows.flatMap renderRow

end Internal

/-- Decode one complete CSV file. Reject malformed fields or record separators. -/
def decode : Bytes → Option Rows
  | [] => some []
  | b :: bs => (readRecords (b :: bs)).map fun (row, rows) => row :: rows

/-- Encode ASCII field data with every field quoted and every row terminated
    by CRLF. Reject empty rows and unrepresentable field bytes. -/
def encode (rows : Rows) : Option Bytes :=
  if rows.all (fun row => !row.isEmpty && row.all (·.all fieldData)) then some (render rows)
  else none

end Silmaril.Formats.Csv
