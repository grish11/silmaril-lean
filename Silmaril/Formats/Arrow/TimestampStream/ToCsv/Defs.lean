module

public import Silmaril.Formats.Arrow.TimestampStream.Defs
public import Silmaril.Formats.Csv.EventStream.Defs
public import Silmaril.Formats.Csv.Typed.Codecs.Defs

/-! Export a checked single-column Arrow TIMESTAMP stream as exact CSV ticks. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.TimestampStream.ToCsv

open Silmaril.Relational Silmaril.Numeric.Timestamp
open Silmaril.Formats.Relational.NamedTable (Packed)

structure Kind where
  unit : TickUnit
  timezone : Option String
  nullable : Bool
  deriving DecidableEq

def Kind.metadata (kind : Kind) : ColumnarTimestamp.Arrow.Metadata := ⟨kind.unit, kind.timezone⟩

abbrev Cell (kind : Kind) := Ticks kind.metadata.kind kind.unit

/-- Preserve the exact descriptor separately from its UTF-8 CSV header. -/
def schemaOf (binding : TimestampBatch.Binding) : Csv.Typed.Schema Kind :=
  ⟨1, fun _ => (binding.name.toByteArray.data.toList,
    ⟨binding.metadata.unit, binding.metadata.timezone, binding.nullable⟩)⟩

/-- Each slot becomes one row. Empty batches contribute zero rows. -/
def rows (stream : Stream) : Csv.Typed.Table (schemaOf stream.binding) Cell :=
  stream.batches.flatten.map fun slot _ => slot

/-- Use the original unit and interpretation when reading or writing signed ticks. -/
def codecs (kind : Kind) : Csv.Typed.CellCodec (Cell kind) where
  print value := (value.toInt64 kind.unit).toOption.map Csv.Typed.Codecs.int64Text
  parse field := (Csv.Typed.Codecs.parseInt64 field).map (Ticks.ofInt64 kind.metadata.kind kind.unit)

structure CsvLimits where
  maxRows : Nat
  maxBytes : Nat

inductive Error where
  | nameConflict
  | input (reason : TimestampStream.Error)
  | rowLimit
  | csv (reason : Csv.EventStream.Error TimestampStream.Error)
  | byteLimit
  deriving DecidableEq

/-- Read to exact EOS at a vacant name. Check the row cap before CSV encoding
and the byte cap before returning the named update, descriptor and CSV bytes. -/
def convert {Name : Type*} [DecidableEq Name] (db : Packed Name Csv.Field Cell) (name : Name)
    (ipcLimits : Arrow.Limits) (csvLimits : CsvLimits) (input : KBytes) :
    Except Error (Csv.EventStream.Result Name Cell) :=
  if (db name).isSome then .error .nameConflict
  else
    match TimestampStream.read ipcLimits input with
    | .error reason => .error (.input reason)
    | .ok stream =>
      let schema := schemaOf stream.binding
      let table := rows stream
      if csvLimits.maxRows < table.length then .error .rowLimit
      else
        match Csv.EventStream.convertCollected (SourceError := TimestampStream.Error) db name schema codecs
            (.ok ⟨⟨schema, table⟩, .eos⟩) with
        | .error reason => .error (.csv reason)
        | .ok result =>
          if csvLimits.maxBytes < result.wire.length then .error .byteLimit
          else .ok result

end Silmaril.Formats.Arrow.TimestampStream.ToCsv
