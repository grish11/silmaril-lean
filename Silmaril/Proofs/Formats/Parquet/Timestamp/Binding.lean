module

public import Silmaril.Formats.Parquet.Timestamp.Defs

namespace Silmaril.Proofs.Formats.Parquet.Timestamp

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.ThriftCompact.Traversal (Reader Field)

public theorem readMetadata_selects {limits : Footer.Limits} {index : Nat} {bytes : Bytes}
    {binding : Binding} (read : Timestamp.readMetadata limits index bytes = .ok binding) :
    let reader : Reader := ⟨bytes, limits.compact, limits.varintMode⟩
    bytes.length ≤ limits.maxFooterBytes ∧
      (index ≠ 0 ∧ binding.leaf.physicalType = some .int64 ∧
        binding.leaf.numChildren.getD 0 = 0 ∧ binding.leaf.repetition.isSome = true) ∧
      ∃ footer schema fields,
        Footer.readMetadata limits bytes = .ok footer ∧ footer.schema[index]? = some binding.leaf ∧
        Internal.schemaFields reader = .ok schema ∧ schema[index]? = some fields ∧
        Internal.annotation reader fields = .ok binding.descriptor := by
  dsimp only
  unfold Timestamp.readMetadata at read
  split at read
  · contradiction
  · rename_i size
    cases metadata : Footer.readMetadata limits bytes with
    | error error => simp [metadata, Except.mapError, bind, Except.bind] at read
    | ok footer =>
      simp only [metadata, Except.mapError, bind, Except.bind] at read
      cases node : footer.schema[index]? with
      | none => simp [node, throw] at read
      | some leaf =>
        rw [node] at read
        dsimp at read
        split at read
        · rename_i checked
          let reader : Reader := ⟨bytes, limits.compact, limits.varintMode⟩
          change (show Except Timestamp.Error Binding from do
            let schema ← Internal.schemaFields reader
            let some fields := schema[index]? | throw (.schemaIndex index)
            let descriptor ← Internal.annotation reader fields
            return ⟨leaf, descriptor⟩) = .ok binding at read
          cases raw : Internal.schemaFields reader with
          | error error => simp [raw, bind, Except.bind] at read
          | ok schema =>
            simp only [raw, bind, Except.bind] at read
            cases selected : schema[index]? with
            | none => simp [selected, throw] at read
            | some fields =>
              rw [selected] at read
              dsimp at read
              cases annotation : Internal.annotation reader fields with
              | error error => simp [annotation] at read
              | ok descriptor =>
                simp only [annotation, pure, Except.pure, Except.ok.injEq] at read
                subst binding
                exact ⟨Nat.le_of_not_gt size, checked, footer, schema, fields,
                  rfl, node, rfl, selected, annotation⟩
        · contradiction

public theorem annotation_uses_modern {reader : Reader} {fields : List Field} {descriptor : Descriptor}
    (read : Internal.annotation reader fields = .ok descriptor) :
    ∃ modern, Internal.requiredField fields 10 = .ok modern ∧
      Internal.logicalTimestamp reader modern = .ok descriptor ∧
      (Internal.optionalField fields 6 = .ok none ∨ ∃ legacy code,
        Internal.optionalField fields 6 = .ok (some legacy) ∧
        Internal.integer reader legacy = .ok code ∧ compatibleConvertedType descriptor.unit code = true) := by
  unfold Internal.annotation at read
  cases field : Internal.requiredField fields 10 with
  | error error => simp [field, bind, Except.bind] at read
  | ok modern =>
    simp only [field, bind, Except.bind] at read
    cases logical : Internal.logicalTimestamp reader modern with
    | error error => simp [logical] at read
    | ok value =>
      rw [logical] at read
      dsimp at read
      cases converted : Internal.optionalField fields 6 with
      | error error => simp [converted] at read
      | ok optional =>
        rw [converted] at read
        cases optional with
        | none =>
          simp only [Except.pure, pure, Except.ok.injEq] at read
          subst descriptor
          exact ⟨modern, rfl, logical, Or.inl rfl⟩
        | some legacy =>
          dsimp at read
          cases legacyCode : Internal.integer reader legacy with
          | error error => simp [legacyCode] at read
          | ok code =>
            rw [legacyCode] at read
            dsimp at read
            split at read
            · rename_i compatible
              simp only [Except.pure, pure, Except.ok.injEq] at read
              subst descriptor
              exact ⟨modern, rfl, logical, Or.inr ⟨legacy, code, rfl, legacyCode, compatible⟩⟩
            · contradiction

public theorem readFooter_selects {limits : Footer.Limits} {index : Nat} {file : Bytes}
    {binding : Binding} (read : Timestamp.readFooter limits index file = .ok binding) :
    ∃ span, Footer.locate limits.maxFooterBytes file = .ok span ∧
      Timestamp.readMetadata limits index (Footer.fileBytes file span.start span.stop) = .ok binding := by
  cases found : Footer.locate limits.maxFooterBytes file with
  | error error => simp [Timestamp.readFooter, found, Except.mapError, bind, Except.bind] at read
  | ok span =>
    exact ⟨span, rfl, by simpa [Timestamp.readFooter, found, Except.mapError, bind, Except.bind] using read⟩

end Silmaril.Proofs.Formats.Parquet.Timestamp
