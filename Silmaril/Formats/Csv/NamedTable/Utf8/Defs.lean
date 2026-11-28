module

public import Silmaril.Formats.Csv.NamedTable.Defs
public import Silmaril.Formats.Csv.Typed.Utf8.Defs

/-! Named nullable tables at the typed UTF-8 CSV boundary. -/

@[expose] public section

namespace Silmaril.Formats.Csv.NamedTable.Utf8

open Silmaril.Formats.Relational.NamedTable (Packed ImportError)

variable {Name Kind : Type*} {Value : Kind → Type*}

/-- Decode UTF-8 CSV under the declared schema and offer it to the existing
named insertion policy. Success requires a vacant name and an exact schema. -/
def importCsv [DecidableEq Name] [DecidableEq Kind] (db : Packed Name Field Value)
    (name : Name) (expected declared : Typed.Schema Kind)
    (codecs : (kind : Kind) → Typed.CellCodec (Value kind)) (wire : Bytes) :
    Except (ImportError Typed.Error) (Packed Name Field Value) :=
  Internal.importDecoded db name expected declared (Typed.Utf8.decode declared codecs wire)

/-- Export the observed table as UTF-8 CSV and carry the ordered schema
alongside the bytes. -/
def exportCsv (db : Packed Name Field Value) (name : Name)
    (codecs : (kind : Kind) → Typed.CellCodec (Value kind)) :
    Except ExportError (Typed.Schema Kind × Bytes) :=
  Internal.exportWith db name fun table => Typed.Utf8.encode table.schema codecs table.rows

end Silmaril.Formats.Csv.NamedTable.Utf8
