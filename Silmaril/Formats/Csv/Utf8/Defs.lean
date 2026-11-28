module

public import Silmaril.Formats.Csv.Defs
public import Init.Data.String.Basic

/-! # UTF-8 CSV over ASCII separators

This profile uses RFC 4180 §2 framing and quoting, and extends its field
alphabet with non-ASCII UTF-8 scalars. Validation is per unescaped field.
The strict ASCII interface is `Silmaril.Formats.Csv`.
-/

@[expose] public section

namespace Silmaril.Formats.Csv.Utf8

open Silmaril.Formats.Csv.Internal (fieldDataFor readRecords render)

/-- The unescaped field uses the extended alphabet and encodes UTF-8. -/
def fieldOK (field : Field) : Bool :=
  field.all (fieldDataFor .utf8Bytes) && ByteArray.validateUTF8 ⟨field.toArray⟩

/-- Every record has at least one field and each field is representable. -/
def rowsOK (rows : Rows) : Bool := rows.all (fun row => !row.isEmpty && row.all fieldOK)

/-- Scan the same comma, quote and CRLF grammar using the extended byte alphabet. -/
def Internal.scan : Bytes → Option Rows
  | [] => some []
  | b :: bs => (readRecords (b :: bs) .utf8Bytes).map fun (row, rows) => row :: rows

/-- Decode lexical rows and reject malformed UTF-8 in any field. -/
def decode (wire : Bytes) : Option Rows := do
  let rows ← Internal.scan wire
  if rowsOK rows then some rows else none

/-- Quote every field and use CRLF after every row, checking representability. -/
def encode (rows : Rows) : Option Bytes :=
  if rowsOK rows then some (render rows) else none

end Silmaril.Formats.Csv.Utf8
