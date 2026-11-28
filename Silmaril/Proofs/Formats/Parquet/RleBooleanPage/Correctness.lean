module

public import Silmaril.Formats.Parquet.RleBooleanPage.Defs
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Hybrid.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms

namespace Silmaril.Proofs.Formats.Parquet.RleBooleanPage

open Silmaril.Formats
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RleBooleanPage

private theorem mapError_ok_iff {ε δ α : Type} {action : Except ε α} {f : ε → δ} {value : α} :
    action.mapError f = .ok value ↔ action = .ok value := by
  cases action <;> simp [Except.mapError]

private theorem bind_ok_iff {ε α β : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} :
    (action >>= next) = .ok output ↔
      ∃ input, action = .ok input ∧ next input = .ok output := by
  cases action <;> simp [Bind.bind, Except.bind]

public theorem readValues_ok_iff {expected : Nat} {limits : Hybrid.Limits}
    {source : Bytes} {values : List Bool} :
    readValues expected limits source = .ok values ↔ ValuesWire expected limits source values := by
  unfold readValues ValuesWire
  constructor
  · intro h
    obtain ⟨⟨lengthWord, payload⟩, split, read⟩ := bind_ok_iff.mp h
    obtain ⟨size, extent⟩ := Hybrid.takeExact_ok_iff.mp (mapError_ok_iff.mp split)
    by_cases exactSize : KBytes.leVal lengthWord = payload.length
    · simp only [ite_eq_left exactSize] at read
      obtain ⟨raw, hybrid, mapped⟩ := bind_ok_iff.mp read
      obtain ⟨_, count, allowed, cap, wire⟩ := Hybrid.decode_ok_iff.mp (mapError_ok_iff.mp hybrid)
      exact ⟨count, allowed, lengthWord, payload, raw, size, extent, exactSize,
        by simpa using cap, by simpa using wire, (Except.ok.inj mapped).symm⟩
    · simp [exactSize, throw] at read
  · rintro ⟨count, allowed, lengthWord, payload, raw, size, extent, exactSize, cap, wire, rfl⟩
    refine bind_ok_iff.mpr ⟨(lengthWord, payload), mapError_ok_iff.mpr (Hybrid.takeExact_ok_iff.mpr
      ⟨size, extent⟩), ?_⟩
    simp only [ite_eq_left exactSize]
    refine bind_ok_iff.mpr ⟨raw, mapError_ok_iff.mpr (Hybrid.decode_ok_iff.mpr
      ⟨by decide, count, allowed, by simpa using cap, by simpa using wire⟩), rfl⟩

public theorem readValues_length {expected : Nat} {limits : Hybrid.Limits}
    {source : Bytes} {values : List Bool} (h : readValues expected limits source = .ok values) :
    values.length = expected := by
  obtain ⟨count, allowed, _, payload, raw, _, _, _, cap, wire, rfl⟩ := readValues_ok_iff.mp h
  have decoded : Hybrid.decode 1 expected limits (Bytes.ofList payload) = .ok raw :=
    Hybrid.decode_ok_iff.mpr ⟨by decide, count, allowed, by simpa using cap, by simpa using wire⟩
  simpa using Hybrid.decode_length decoded

public theorem decode_ok_iff {physical : Footer.PhysicalType} {params : ScalarPage.Parameters}
    {limits : Limits} {source : Bytes} {output : List (Option Bool)} :
    decode physical params limits source = .ok output ↔
      physical = .boolean ∧ ∃ (page : ScalarPage.Prepared) (values : List Bool),
        ScalarPage.prepareFor 3 params limits.page source = .ok page ∧
        readValues (page.mask.count true) limits.values page.scalars = .ok values ∧
        output.map Option.isSome = page.mask ∧ output.filterMap id = values := by
  unfold decode
  by_cases typed : physical = .boolean
  · simp only [typed, true_and]
    constructor
    · intro h
      obtain ⟨page, prepared, h⟩ := bind_ok_iff.mp h
      obtain ⟨values, read, rebuilt⟩ := bind_ok_iff.mp h
      exact ⟨page, values, mapError_ok_iff.mp prepared, read,
        FlatPage.reconstruct_ok_iff.mp (mapError_ok_iff.mp rebuilt)⟩
    · rintro ⟨page, values, prepared, read, shape, order⟩
      exact bind_ok_iff.mpr ⟨page, mapError_ok_iff.mpr prepared,
        bind_ok_iff.mpr ⟨values, read, mapError_ok_iff.mpr
          (FlatPage.reconstruct_ok_iff.mpr ⟨shape, order⟩)⟩⟩
  · simp [typed, throw]

public theorem decode_wire_sound {physical : Footer.PhysicalType} {params : ScalarPage.Parameters}
    {limits : Limits} {source : Bytes} {output : List (Option Bool)}
    (h : decode physical params limits source = .ok output) :
    physical = .boolean ∧ params.encoding = 3 ∧
      ∃ (layout : FlatPage.Layout) (page : ScalarPage.Prepared),
        ScalarPage.validateFor 3 params limits.page source = .ok layout ∧
        ScalarPage.PreparedWire params limits.page layout source page ∧
        output.map Option.isSome = page.mask ∧
        ValuesWire (page.mask.count true) limits.values page.scalars (output.filterMap id) := by
  obtain ⟨typed, page, values, prepared, read, shape, order⟩ := decode_ok_iff.mp h
  obtain ⟨layout, valid, wire⟩ := ScalarPage.prepareFor_sound prepared
  have encoding : params.encoding = 3 := by
    by_contra unequal
    simp [ScalarPage.validateFor, unequal] at valid
  rw [order]
  exact ⟨typed, encoding, layout, page, valid, wire, shape, readValues_ok_iff.mp read⟩

public theorem decode_counts {physical : Footer.PhysicalType} {params : ScalarPage.Parameters}
    {limits : Limits} {source : Bytes} {output : List (Option Bool)}
    (h : decode physical params limits source = .ok output) :
    output.length = params.numValues ∧
      (output.filterMap id).length = (output.map Option.isSome).count true ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => (output.filterMap id).length = params.numValues - nulls := by
  obtain ⟨_, page, values, prepared, read, shape, order⟩ := decode_ok_iff.mp h
  obtain ⟨count, present⟩ := ScalarPage.preparedFor_counts prepared
  have total : output.length = params.numValues := by
    simpa [count] using congrArg List.length shape
  have kept := readValues_length read
  rw [order, shape]
  refine ⟨total, kept, ?_⟩
  cases version : params.version with
  | v1 => trivial
  | v2 =>
    rw [version] at present
    exact kept.trans present

end Silmaril.Proofs.Formats.Parquet.RleBooleanPage
