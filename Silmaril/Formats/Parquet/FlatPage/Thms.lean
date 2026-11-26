module

public import Silmaril.Formats.Parquet.FlatPage.Defs
import Silmaril.Proofs.Formats.Parquet.FlatPage.Levels
import Silmaril.Proofs.Formats.Parquet.FlatPage.Reconstruct
import Silmaril.Proofs.Formats.Parquet.FlatPage.Decode

/-! Exact definition section consumption and ordered flat-slot reconstruction. -/

public section

namespace Silmaril.Formats.Parquet.FlatPage

/-- A successful optional V1 split accounts for the length word, the declared
definition bytes, and the entire remaining scalar slice. -/
theorem splitV1Optional_ok_iff {byteLimit : Nat} {source : Bytes} {sections : Sections} :
    splitV1Optional byteLimit source = .ok sections ↔
      ∃ lengthBytes : List UInt8, lengthBytes.length = 4 ∧
        KBytes.leVal lengthBytes = sections.definitions.length ∧
        sections.definitions.length ≤ byteLimit ∧
        source.toList = lengthBytes ++ sections.definitions.toList ++ sections.scalars.toList :=
  Proofs.Formats.Parquet.FlatPage.splitV1Optional_ok_iff

/-- A successful V2 split admits exactly the separately delimited sections
with zero repetition bytes and the declared bounded definition length. -/
theorem splitV2_ok_iff {layout : Layout} {byteLimit repetitionBytes definitionBytes : Nat}
    {definitions scalars : Bytes} {sections : Sections} :
    split layout byteLimit (.v2 repetitionBytes definitionBytes definitions scalars) = .ok sections ↔
      repetitionBytes = 0 ∧ definitionBytes = definitions.length ∧
      definitionBytes < Hybrid.runLimit ∧ definitionBytes ≤ byteLimit ∧
      sections = ⟨definitions, scalars⟩ :=
  Proofs.Formats.Parquet.FlatPage.splitV2_ok_iff

/-- The bounded reader implements the required-empty or exact hybrid wire relation. -/
theorem readMask_ok_iff {layout : Layout} {slots : Nat} {limits : Hybrid.Limits}
    {definitions : Bytes} {mask : List Bool} :
    readMask layout slots limits definitions = .ok mask ↔
      slots < Hybrid.runLimit ∧ slots ≤ limits.values ∧ definitions.length ≤ limits.bytes ∧
        MaskWire layout slots definitions mask :=
  Proofs.Formats.Parquet.FlatPage.readMask_ok_iff

theorem readMask_length {layout : Layout} {slots : Nat} {limits : Hybrid.Limits}
    {definitions : Bytes} {mask : List Bool}
    (h : readMask layout slots limits definitions = .ok mask) : mask.length = slots :=
  Proofs.Formats.Parquet.FlatPage.readMask_length h

theorem plan_sound {schema : LevelSchema} {slots present : Nat} {limits : Hybrid.Limits}
    {body : Body} {checked : Plan} (h : plan schema slots present limits body = .ok checked) :
    ∃ layout sections, schema.layout? = some layout ∧
      split layout limits.bytes body = .ok sections ∧
      readMask layout slots limits sections.definitions = .ok checked.mask ∧
      checked.scalars = sections.scalars ∧ checked.mask.count true = present :=
  Proofs.Formats.Parquet.FlatPage.plan_sound h

/-- Reconstructing projects the original mask and preserves the scalar list in wire order. -/
theorem reconstruct_ok_iff {α : Type} {mask : List Bool} {values : List α}
    {slots : List (Option α)} :
    reconstruct mask values = .ok slots ↔
      slots.map Option.isSome = mask ∧ slots.filterMap id = values :=
  Proofs.Formats.Parquet.FlatPage.reconstruct_ok_iff

theorem reconstruct_exists_iff {α : Type} (mask : List Bool) (values : List α) :
    (∃ slots, reconstruct mask values = .ok slots) ↔ mask.count true = values.length :=
  Proofs.Formats.Parquet.FlatPage.reconstruct_exists_iff mask values

/-- A complete decode fills exactly the checked mask with the scalars returned
by the physical decoder, in their original order. -/
theorem decode_ok_iff {α ε : Type} {schema : LevelSchema} {slots present : Nat}
    {limits : Hybrid.Limits} {body : Body} {scalar : Nat → Bytes → Except ε (List α)}
    {output : List (Option α)} :
    decode schema slots present limits body scalar = .ok output ↔
      ∃ checked values, plan schema slots present limits body = .ok checked ∧
        scalar present checked.scalars = .ok values ∧
        output.map Option.isSome = checked.mask ∧ output.filterMap id = values :=
  Proofs.Formats.Parquet.FlatPage.decode_ok_iff

theorem decode_counts {α ε : Type} {schema : LevelSchema} {slots present : Nat}
    {limits : Hybrid.Limits} {body : Body} {scalar : Nat → Bytes → Except ε (List α)}
    {output : List (Option α)} (h : decode schema slots present limits body scalar = .ok output) :
    output.length = slots ∧ (output.filterMap id).length = present :=
  Proofs.Formats.Parquet.FlatPage.decode_counts h

/-- After level validation, decoding succeeds exactly when the callback
succeeds with the requested number of present scalars. -/
theorem decode_exists_iff {α ε : Type} (schema : LevelSchema) (slots present : Nat)
    (limits : Hybrid.Limits) (body : Body) (scalar : Nat → Bytes → Except ε (List α)) :
    (∃ output, decode schema slots present limits body scalar = .ok output) ↔
      ∃ checked values, plan schema slots present limits body = .ok checked ∧
        scalar present checked.scalars = .ok values ∧ values.length = present :=
  Proofs.Formats.Parquet.FlatPage.decode_exists_iff schema slots present limits body scalar

end Silmaril.Formats.Parquet.FlatPage
