module

public import Silmaril.Formats.Parquet.LegacyBitPackedV1.Defs
import Silmaril.Formats.Parquet.BitPackedLevels.Thms
import Silmaril.Formats.Parquet.Payload.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.LegacyBitPackedV1

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.LegacyBitPackedV1

public theorem admit_sound {physical : Footer.PhysicalType} {schema : FlatPage.LevelSchema}
    {codec : Int} {header : Page.Header} {info : Page.DataV1}
    (h : admit physical schema codec header = .ok info) : Profile physical schema codec header info := by
  unfold admit at h
  split at h
  · contradiction
  · rename_i shape
    simp only [not_or, not_not] at shape
    obtain ⟨physicalType, repetitions, definitions⟩ := shape
    have optional : schema = ⟨0, 1⟩ := by
      cases schema
      simp_all
    split at h
    · contradiction
    · rename_i uncompressed
      split at h
      · contradiction
      · rename_i crc
        cases kind : header.kind with
        | dataV1 raw =>
          simp only [kind] at h
          split at h
          · contradiction
          · rename_i plain
            split at h
            · contradiction
            · rename_i levels
              simp only [not_or, not_not] at levels
              cases h
              exact ⟨physicalType, optional, not_not.mp uncompressed, not_not.mp crc, kind,
                not_not.mp plain, levels.1, levels.2⟩
        | dictionary _ | dataV2 _ | skipped _ => simp [kind] at h

private theorem mapError_ok_iff {ε δ α : Type} {action : Except ε α} {f : ε → δ} {value : α} :
    action.mapError f = .ok value ↔ action = .ok value := by
  cases action <;> simp [Except.mapError]

private theorem bind_ok_iff {ε α β : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} :
    (action >>= next) = .ok output ↔
      ∃ input, action = .ok input ∧ next input = .ok output := by
  cases action <;> simp [Bind.bind, Except.bind]

public theorem prepare_sound {physical : Footer.PhysicalType} {schema : FlatPage.LevelSchema}
    {codec : Int} {header : Page.Header} {limits : ScalarPage.Limits} {body : Bytes}
    {page : Prepared} (h : prepare physical schema codec header limits body = .ok page) :
    ∃ info, Profile physical schema codec header info ∧ PreparedWire header info limits body page := by
  unfold prepare at h
  obtain ⟨info, admitted, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨raw, payload, h⟩ := bind_ok_iff.mp h
  obtain ⟨⟨levels, values⟩, levelRead, h⟩ := bind_ok_iff.mp h
  cases h
  have profile := admit_sound admitted
  obtain ⟨selected, matched, wire, compressed, storedCap, expanded, outputCap⟩ :=
    Payload.decode_sound (mapError_ok_iff.mp payload)
  have uncompressed : selected = .uncompressed := by
    simpa [profile.uncompressed, Payload.Codec.ofId] using matched.symm
  subst selected
  cases wire
  have read := mapError_ok_iff.mp levelRead
  rw [Bytes.ofList_toList] at read
  obtain ⟨_, _, slots, bytes, definitions, whole, levelsWire⟩ := BitPackedLevels.readPrefix_ok_iff.mp read
  exact ⟨info, profile, ⟨by simpa [ScalarPage.Limits.payloadBounds] using compressed,
    by simpa [ScalarPage.Limits.payloadBounds] using expanded,
    by simpa [ScalarPage.Limits.payloadBounds] using storedCap,
    by simpa [ScalarPage.Limits.payloadBounds] using outputCap, slots,
    definitions, levelsWire.extent ▸ bytes, whole, levelsWire⟩⟩

public theorem decode_ok_iff {physical : Footer.PhysicalType} {schema : FlatPage.LevelSchema}
    {codec : Int} {header : Page.Header} {limits : ScalarPage.Limits} {body : Bytes} {result : Decoded} :
    decodeInt32 physical schema codec header limits body = .ok result ↔
      ∃ (page : Prepared) (values : List Int32),
        prepare physical schema codec header limits body = .ok page ∧
        Plain.decodeInt32 (page.mask.count true) page.values = .ok values ∧
        result.slots.map Option.isSome = page.mask ∧ result.slots.filterMap id = values ∧
        result.nullCount = page.mask.count false := by
  unfold decodeInt32
  constructor
  · intro h
    obtain ⟨page, prepared, h⟩ := bind_ok_iff.mp h
    obtain ⟨values, read, h⟩ := bind_ok_iff.mp h
    obtain ⟨slots, rebuilt, h⟩ := bind_ok_iff.mp h
    cases h
    obtain ⟨shape, order⟩ := FlatPage.reconstruct_ok_iff.mp (mapError_ok_iff.mp rebuilt)
    exact ⟨page, values, prepared, mapError_ok_iff.mp read, shape, order, rfl⟩
  · rintro ⟨page, values, prepared, read, shape, order, nulls⟩
    refine bind_ok_iff.mpr ⟨page, prepared, ?_⟩
    refine bind_ok_iff.mpr ⟨values, mapError_ok_iff.mpr read, ?_⟩
    refine bind_ok_iff.mpr ⟨result.slots, mapError_ok_iff.mpr
      (FlatPage.reconstruct_ok_iff.mpr ⟨shape, order⟩), ?_⟩
    cases result
    simp_all only [pure, Except.pure]

private theorem mask_present (page : Prepared) : page.mask.count true = page.levels.count 1 := by
  simp [Prepared.mask, List.count_eq_countP, Function.comp_def]

private theorem mask_absent {page : Prepared} (bounds : ∀ level ∈ page.levels, level ≤ 1) :
    page.mask.count false = page.levels.count 0 := by
  simp only [Prepared.mask, List.count_eq_countP, List.countP_map]
  apply List.countP_congr
  intro level member
  have atMostOne := bounds level member
  have binary : level = 0 ∨ level = 1 := by omega
  rcases binary with equality | equality <;> simp [equality]

public theorem decode_wire_sound {physical : Footer.PhysicalType} {schema : FlatPage.LevelSchema}
    {codec : Int} {header : Page.Header} {limits : ScalarPage.Limits} {body : Bytes} {result : Decoded}
    (h : decodeInt32 physical schema codec header limits body = .ok result) :
    ∃ (info : Page.DataV1) (page : Prepared) (words : List (List UInt8)),
      Profile physical schema codec header info ∧ PreparedWire header info limits body page ∧
      page.values.toList = words.flatten ∧ words.length = page.levels.count 1 ∧
      (∀ word ∈ words, word.length = 4) ∧ result.slots.map Option.isSome = page.mask ∧
      result.slots.filterMap id = words.map (fun word => (Plain.readUInt32Word word).toInt32) ∧
      result.nullCount = page.levels.count 0 := by
  obtain ⟨page, values, prepared, read, shape, order, nulls⟩ := decode_ok_iff.mp h
  obtain ⟨info, profile, wire⟩ := prepare_sound prepared
  obtain ⟨_, _, _, levels⟩ := wire.sections
  obtain ⟨_, words, splits, count, widths, mapped⟩ :=
    Plain.decodeFixedWidth_ok_iff.mp (by
      simpa only [Plain.decodeInt32] using read)
  exact ⟨info, page, words, profile, wire, splits, count.trans (mask_present page), widths,
    shape, order.trans mapped, nulls.trans (mask_absent levels.bounds)⟩

public theorem decode_counts {physical : Footer.PhysicalType} {schema : FlatPage.LevelSchema}
    {codec : Int} {header : Page.Header} {limits : ScalarPage.Limits} {body : Bytes} {result : Decoded}
    (h : decodeInt32 physical schema codec header limits body = .ok result) :
    ∃ info : Page.DataV1, header.kind = .dataV1 info ∧ result.slots.length = info.numValues ∧
      result.nullCount = result.slots.countP Option.isNone ∧
      result.nullCount = info.numValues - (result.slots.filterMap id).length := by
  obtain ⟨page, _, prepared, _, shape, _, nulls⟩ := decode_ok_iff.mp h
  obtain ⟨info, profile, wire⟩ := prepare_sound prepared
  obtain ⟨_, _, _, levels⟩ := wire.sections
  have length : result.slots.length = info.numValues := by
    simpa [Prepared.mask, levels.countFits] using congrArg List.length shape
  have nullSlots : (result.slots.map Option.isSome).count false = result.slots.countP Option.isNone := by
    simp only [List.count_eq_countP, List.countP_map]
    apply List.countP_congr
    intro slot _
    cases slot <;> simp
  rw [shape, ← nulls] at nullSlots
  have total := List.length_eq_countP_add_countP Option.isSome (l := result.slots)
  have present : (result.slots.filterMap id).length = result.slots.countP Option.isSome :=
    List.length_filterMap_eq_countP
  have absent : result.slots.countP (fun slot => ¬ slot.isSome) =
      result.slots.countP Option.isNone := by
    apply List.countP_congr
    intro slot _
    cases slot <;> simp
  rw [length, ← present, absent, ← nullSlots] at total
  exact ⟨info, profile.v1, length, nullSlots, by omega⟩

end Silmaril.Proofs.Formats.Parquet.LegacyBitPackedV1
