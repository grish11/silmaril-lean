module

public import Silmaril.Formats.Arrow.Writer.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.File.Defs
public import Silmaril.Formats.Relational.BinaryObservation.Defs

/-! Exhaust one checked PLAIN BYTE_ARRAY leaf and prepare its opaque slots
for a single-field BinaryView stream. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc

open Parquet
open Relational.BinaryObservation (Field)

inductive SourceError where
  | openError (cause : File.Error)
  | readError (cause : FlatColumn.Error File.PageError)
  deriving DecidableEq, Repr

/-- One successfully exhausted, explicitly selected file column. -/
structure Source where
  field : Field
  groups : List (List (Option Bytes))

/-- Give the writer the selected name and nullability as a BinaryView field. -/
def Source.ipcField (source : Source) : Arrow.BinaryView.Schema.Field :=
  ⟨source.field.name, source.field.nullable, .binary⟩

/-- Read the original selected groups in footer order. Open and indexed read
errors retain their original causes. -/
def readSource (limits : File.Limits) (input : Bytes) (name : String)
    (layout : FlatColumn.Layout) : Except SourceError Source := do
  let checked ← (File.openFile limits input name layout).mapError .openError
  let groups ← ((List.range checked.snapshot.groupCount).mapM (checked.readGroup limits)).mapError .readError
  return ⟨⟨name, decide (layout = .optional)⟩, groups⟩

/-- The same opaque octets in the writer's byte-tree carrier. -/
def packValue (value : Bytes) : KBytes :=
  Arrow.Writer.emitWords 1 (value.toList.map UInt8.toNat)

/-- One batch per source group, including empty groups. -/
def Source.batches (source : Source) : List (List (Option KBytes)) :=
  source.groups.map (List.map (Option.map packValue))

end Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc
