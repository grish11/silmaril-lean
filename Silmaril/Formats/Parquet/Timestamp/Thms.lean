module

public import Silmaril.Formats.Parquet.Timestamp.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Binding
import Silmaril.Formats.ColumnarTimestamp.Wire.Thms

/-! # Checked schema selection and value-slice round trip -/

public section

namespace Silmaril.Formats.Parquet.Timestamp

open Numeric.Timestamp
open ThriftCompact.Traversal (Reader Field)

/-- The binding uses the same schema ordinal in the typed and compact views of
    the exact metadata slice. The selected entry is a non-root INT64 leaf. -/
theorem readMetadataWith_selects {profile : AnnotationProfile} {limits : Footer.Limits} {index : Nat} {bytes : Bytes}
    {binding : Binding} (read : readMetadataWith profile limits index bytes = .ok binding) :
    let reader : Reader := ⟨bytes, limits.compact, limits.varintMode⟩
    bytes.length ≤ limits.maxFooterBytes ∧
      (index ≠ 0 ∧ binding.leaf.physicalType = some .int64 ∧
        binding.leaf.numChildren.getD 0 = 0 ∧ binding.leaf.repetition.isSome = true) ∧
      ∃ footer schema fields,
        Footer.readMetadata limits bytes = .ok footer ∧ footer.schema[index]? = some binding.leaf ∧
        Internal.schemaFields reader = .ok schema ∧ schema[index]? = some fields ∧
        Internal.annotationWith profile reader fields = .ok binding.descriptor :=
  Proofs.Formats.Parquet.Timestamp.readMetadataWith_selects read

/-- The binding uses the same schema ordinal in the typed and compact views of
    the exact metadata slice. The selected entry is a non-root INT64 leaf. -/
theorem readMetadata_selects {limits : Footer.Limits} {index : Nat} {bytes : Bytes}
    {binding : Binding} (read : readMetadata limits index bytes = .ok binding) :
    let reader : Reader := ⟨bytes, limits.compact, limits.varintMode⟩
    bytes.length ≤ limits.maxFooterBytes ∧
      (index ≠ 0 ∧ binding.leaf.physicalType = some .int64 ∧
        binding.leaf.numChildren.getD 0 = 0 ∧ binding.leaf.repetition.isSome = true) ∧
      ∃ footer schema fields,
        Footer.readMetadata limits bytes = .ok footer ∧ footer.schema[index]? = some binding.leaf ∧
        Internal.schemaFields reader = .ok schema ∧ schema[index]? = some fields ∧
        Internal.annotation reader fields = .ok binding.descriptor :=
  readMetadataWith_selects (profile := .modernOnly) read

/-- With a present modern field, the opt-in profile uses the same checked
modern parser, including all dual-annotation checks. -/
theorem annotationWith_modern {reader : Reader} {fields : List Field} {modern : Field}
    (present : Internal.optionalField fields 10 = .ok (some modern)) :
    Internal.annotationWith .allowConvertedOnly reader fields = Internal.annotation reader fields := by
  simp [Internal.annotationWith, present, Bind.bind, Except.bind]

/-- When field 10 is absent, a successful opt-in reads exactly code 9 or 10
with its historical UTC interpretation. -/
theorem annotationWith_converted {reader : Reader} {fields : List Field} {descriptor : Descriptor}
    (absent : Internal.optionalField fields 10 = .ok none)
    (read : Internal.annotationWith .allowConvertedOnly reader fields = .ok descriptor) :
    ∃ legacy code, Internal.requiredField fields 6 = .ok legacy ∧
      Internal.integer reader legacy = .ok code ∧
      ((code = 9 ∧ descriptor = ⟨.millis, true⟩) ∨ (code = 10 ∧ descriptor = ⟨.micros, true⟩)) :=
  Proofs.Formats.Parquet.Timestamp.annotationWith_converted absent read

/-- The modern annotation always supplies the descriptor. A present legacy tag
    must be compatible with its unit. -/
theorem annotation_uses_modern {reader : Reader} {fields : List Field} {descriptor : Descriptor}
    (read : Internal.annotation reader fields = .ok descriptor) :
    ∃ modern, Internal.requiredField fields 10 = .ok modern ∧
      Internal.logicalTimestamp reader modern = .ok descriptor ∧
      (Internal.optionalField fields 6 = .ok none ∨ ∃ legacy code,
        Internal.optionalField fields 6 = .ok (some legacy) ∧
        Internal.integer reader legacy = .ok code ∧ compatibleConvertedType descriptor.unit code = true) :=
  Proofs.Formats.Parquet.Timestamp.annotation_uses_modern read

/-- A file binding comes from the advertised, bounded plaintext footer span. -/
theorem readFooter_selects {limits : Footer.Limits} {index : Nat} {file : Bytes}
    {binding : Binding} (read : readFooter limits index file = .ok binding) :
    ∃ span, Footer.locate limits.maxFooterBytes file = .ok span ∧
      readMetadata limits index (Footer.fileBytes file span.start span.stop) = .ok binding :=
  Proofs.Formats.Parquet.Timestamp.readFooter_selects read

/-- The descriptor preserves the PLAIN value count and every value byte. -/
theorem Binding.decodePlain_roundtrip {binding : Binding} {count : Nat} {bytes : Bytes}
    {values : List (Ticks binding.descriptor.kind binding.descriptor.unit.tickUnit)}
    (read : binding.decodePlain count bytes = .ok values) :
    values.length = count ∧ binding.descriptor.encodePlain values = .ok bytes :=
  ColumnarTimestamp.Wire.encodeLE_decodeLE read

end Silmaril.Formats.Parquet.Timestamp
