module

public import Silmaril.Formats.Parquet.Footer.Defs
import Silmaril.Proofs.Formats.Parquet.Footer.Contracts

/-! Framing, exact consumption and interval arithmetic for plaintext Parquet footers. -/

public section

namespace Silmaril.Formats.Parquet.Footer

/-- Successful location is equivalent to the plaintext framing relation. -/
theorem locate_ok_iff {limit : Nat} {file : Bytes} {span : Span} :
    locate limit file = .ok span ↔ Framed limit file span :=
  Proofs.Formats.Parquet.Footer.locate_ok_iff

/-- The runtime extraction is the checked in-file slice for any framed span. -/
theorem framed_slice {limit : Nat} {file : Bytes} {span : Span}
    (h : Framed limit file span) :
    file.slice? span.start (some span.stop) = some (fileBytes file span.start span.stop) :=
  Proofs.Formats.Parquet.Footer.framed_slice h

/-- The exact metadata entry point succeeds precisely when the prefix reader ends
at the last byte boundary of its input. -/
theorem readMetadata_ok_iff {limits : Limits} {source : Bytes} {metadata : Metadata} :
    readMetadata limits source = .ok metadata ↔
      readMetadataPrefix ⟨source, limits.compact, limits.varintMode⟩ 0 = .ok (metadata, source.length) :=
  Proofs.Formats.Parquet.Footer.readMetadata_ok_iff

/-- File-level success is equivalent to framing and exact prefix-reader consumption
of the advertised checked slice. -/
theorem readFooter_ok_iff {limits : Limits} {file : Bytes} {span : Span} {metadata : Metadata} :
    readFooter limits file = .ok (span, metadata) ↔
      Framed limits.maxFooterBytes file span ∧ ∃ payload : Bytes,
        file.slice? span.start (some span.stop) = some payload ∧
        readMetadataPrefix ⟨payload, limits.compact, limits.varintMode⟩ 0 =
          .ok (metadata, footerLength file) :=
  Proofs.Formats.Parquet.Footer.readFooter_ok_iff

/-- A checked data span has exactly the advertised signed endpoints and lies
strictly after the leading magic and no later than the start of the footer. -/
theorem checkDataSpan_some_iff {footerStart : Nat} {offset size : Int} {span : Span} :
    checkDataSpan footerStart offset size = some span ↔
      (span.start : Int) = offset ∧ (span.stop : Int) = offset + size ∧
      4 ≤ span.start ∧ span.start < span.stop ∧ span.stop ≤ footerStart :=
  Proofs.Formats.Parquet.Footer.checkDataSpan_some_iff

end Silmaril.Formats.Parquet.Footer
