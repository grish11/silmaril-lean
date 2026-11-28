module

public import Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv.Defs
import Silmaril.Formats.Csv.EventStream.Thms
import Silmaril.Formats.Csv.Typed.Codecs.Thms

public section

namespace Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv

open Silmaril.Relational Silmaril.Formats.Arrow
open Silmaril.Formats.Relational.NamedTable (Packed)

variable {Name : Type*} [DecidableEq Name] {db : Packed Name Csv.Field Cell} {name : Name}
variable {expected : Scan.Schema String Unit} {limits : Limits} {bytes : Bytes}

/-- UTF-8 label translation preserves the original ordered rows and outcome. -/
theorem collect_readEvents (limits : Limits) (schema : Scan.Schema String Unit) (bytes : Bytes) :
    (readEvents limits schema bytes).collect =
      (FlatInt32.readAll limits schema bytes).collect.map (fun observed =>
        ⟨⟨csvSchema observed.table.schema, observed.table.rows⟩, observed.termination⟩) := by
  unfold readEvents
  cases FlatInt32.readAll limits schema bytes <;> rfl

/-- Decoding the CSV after success recovers the exact ordered nullable rows
from the completed read. Only the destination name is updated. -/
theorem convert_roundTrip {result : Csv.EventStream.Result Name Cell}
    (converted : convert db name expected limits bytes = .ok result) :
    ∃ rows : Csv.Typed.Table (csvSchema expected) Cell,
      (readEvents limits expected bytes).collect = .ok ⟨⟨csvSchema expected, rows⟩, .eos⟩ ∧
      result.schema = csvSchema expected ∧
      Csv.Typed.Utf8.decode (csvSchema expected) codecs result.wire = .ok rows ∧
      result.db = Function.update db name (some ⟨csvSchema expected, rows⟩) :=
  Csv.EventStream.convert_roundTrip (fun _ => Csv.Typed.Codecs.int32_parsePrint) converted

/-- A failed Parquet read at a vacant destination returns only the indexed
input error, even if earlier groups produced rows. -/
theorem convert_read_error (vacant : db name = none) {table : Scan.Observation String Cell}
    {error : Snapshot.Error (Error Unit)}
    (failed : (FlatInt32.readAll limits expected bytes).collect = .ok ⟨table, .readError error⟩) :
    convert db name expected limits bytes = .error (.input (.readError error)) := by
  simp only [convert, Csv.EventStream.convert, collect_readEvents, failed, Except.map]
  exact Csv.EventStream.convertCollected_read_error vacant ⟨csvSchema table.schema, table.rows⟩ error

end Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv
