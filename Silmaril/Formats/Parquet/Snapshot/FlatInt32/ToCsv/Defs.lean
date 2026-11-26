module

public import Silmaril.Formats.Parquet.Snapshot.FlatInt32.Defs
public import Silmaril.Formats.Csv.EventStream.Defs
public import Silmaril.Formats.Csv.Typed.Codecs.Defs

/-! Convert checked flat INT32 Parquet bytes through the named UTF-8 CSV API. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Relational.NamedTable (Packed)

/-- Encode the ordered column names as UTF-8, retaining each typed cell position. -/
def csvSchema (schema : Scan.Schema String Unit) : Csv.Typed.Schema Unit :=
  ⟨schema.width, fun i => ((schema.kind i).1.toByteArray.data.toList, (schema.kind i).2)⟩

def codecs (_ : Unit) : Csv.Typed.CellCodec Int32 := Csv.Typed.Codecs.int32

/-- Relabel the stream with UTF-8 field names. Batch contents and the terminal
outcome are carried through unchanged. -/
def readEvents (limits : Limits) (schema : Scan.Schema String Unit) (bytes : Bytes) :
    Events.EventStream Csv.Field Cell (Snapshot.Error (Error Unit)) :=
  (FlatInt32.readAll limits schema bytes).map fun ⟨opened, trace⟩ =>
    ⟨csvSchema opened, ⟨trace.batches, trace.termination⟩⟩

/-- Publish the named table and its CSV together after exact-schema EOS and
successful export. A failure returns the typed error alone. -/
def convert {Name : Type*} [DecidableEq Name] (db : Packed Name Csv.Field Cell)
    (name : Name) (expected : Scan.Schema String Unit) (limits : Limits) (bytes : Bytes) :
    Except (Csv.EventStream.Error (Snapshot.Error (Error Unit))) (Csv.EventStream.Result Name Cell) :=
  Csv.EventStream.convert db name (csvSchema expected) codecs (readEvents limits expected bytes)

end Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv
