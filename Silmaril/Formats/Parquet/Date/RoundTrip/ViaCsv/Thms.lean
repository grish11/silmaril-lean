module

public import Silmaril.Formats.Parquet.Date.RoundTrip.ViaCsv.Defs
public import Silmaril.Formats.Parquet.Date.RoundTrip.Defs
import Silmaril.Proofs.Formats.Parquet.Date.RoundTrip.ViaCsv.Readback

public section

namespace Silmaril.Formats.Parquet.Date.RoundTrip.ViaCsv

/-- Successful conversion keeps the checked DATE descriptor and every
ordered nullable signed day. Output has one explicit group, containing
the concatenation of the original footer-ordered groups. -/
theorem convert_readback {limits : Limits} {name : String} {nullable : Bool} {input output : Bytes}
    (converted : convert limits name nullable input = .ok output) :
    ∃ batches, ParquetObserves limits.source input ⟨name, nullable, batches⟩ ∧
      ParquetObserves limits.readback output ⟨name, nullable, [batches.flatten]⟩ :=
  Proofs.Formats.Parquet.Date.RoundTrip.ViaCsv.convert_readback converted

/-- Two successful normalizations agree on output rows exactly when their
input row observations agree under the common declaration. -/
theorem output_rows_eq_iff {limits : Limits} {name : String} {nullable : Bool}
    {left right leftOutput rightOutput : Bytes}
    (convertedLeft : convert limits name nullable left = .ok leftOutput)
    (convertedRight : convert limits name nullable right = .ok rightOutput) :
    Date.ToCsv.readRows limits.readback name nullable leftOutput =
      Date.ToCsv.readRows limits.readback name nullable rightOutput ↔
    Date.ToCsv.readRows limits.source name nullable left =
      Date.ToCsv.readRows limits.source name nullable right :=
  Proofs.Formats.Parquet.Date.RoundTrip.ViaCsv.output_rows_eq_iff convertedLeft convertedRight

end Silmaril.Formats.Parquet.Date.RoundTrip.ViaCsv
