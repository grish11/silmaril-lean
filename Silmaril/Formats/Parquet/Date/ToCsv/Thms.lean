module

public import Silmaril.Formats.Parquet.Date.ToCsv.Defs
public import Silmaril.Formats.Parquet.Date.RoundTrip.Defs
import Silmaril.Proofs.Formats.Parquet.Date.ToCsv.Correctness

public section

namespace Silmaril.Formats.Parquet.Date.ToCsv

/-- Success observes exactly the checked DATE descriptor and the signed
nullable slots in footer order, concatenated across groups. -/
theorem readRows_eq_ok_iff {limits : Date.Limits} {name : String} {nullable : Bool}
    {input : Bytes} {slots : Arrow.DateStream.Writer.Column} :
    readRows limits name nullable input = .ok slots ↔
      ∃ batches, RoundTrip.ParquetObserves limits input ⟨name, nullable, batches⟩ ∧
        slots = batches.flatten :=
  Proofs.Formats.Parquet.Date.ToCsv.readRows_eq_ok_iff

/-- The canonical typed output must satisfy both total CSV caps after source EOF. -/
theorem convert_eq_ok_iff {limits : Date.Limits} {csv : Arrow.DateStream.FromCsv.CsvLimits}
    {name : String} {nullable : Bool} {input : Bytes} {wire : Csv.Bytes} :
    convert limits csv name nullable input = .ok wire ↔
      wire.length ≤ csv.maxBytes ∧
      ∃ slots, readRows limits name nullable input = .ok slots ∧ slots.length ≤ csv.maxRows ∧
        Csv.Typed.Codecs.Date32.encode (Arrow.DateStream.FromCsv.schema name nullable) id
          (Arrow.DateStream.ToCsv.rows name nullable slots) = .ok wire :=
  Proofs.Formats.Parquet.Date.ToCsv.convert_eq_ok_iff

/-- Successful canonical exports under a common declaration are injective
in the ordered nullable signed rows. -/
theorem convert_eq_iff {limits : Date.Limits} {csv : Arrow.DateStream.FromCsv.CsvLimits}
    {name : String} {nullable : Bool} {left right : Bytes} {leftWire rightWire : Csv.Bytes}
    (wroteLeft : convert limits csv name nullable left = .ok leftWire)
    (wroteRight : convert limits csv name nullable right = .ok rightWire) :
    leftWire = rightWire ↔ readRows limits name nullable left = readRows limits name nullable right :=
  Proofs.Formats.Parquet.Date.ToCsv.convert_eq_iff wroteLeft wroteRight

end Silmaril.Formats.Parquet.Date.ToCsv
