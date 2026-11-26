module

public import Silmaril.Formats.Parquet.DeltaLengthByteArray.Defs
import Silmaril.Formats.Parquet.DeltaBinaryPacked.Thms
import Silmaril.Formats.Parquet.Hybrid.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.DeltaLengthByteArray

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.DeltaLengthByteArray

private theorem bind_ok {ε α β : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (h : (action >>= next) = .ok output) :
    ∃ input, action = .ok input ∧ next input = .ok output := by
  cases action with
  | error error => cases h
  | ok value => exact ⟨value, rfl, h⟩

private theorem mapError_ok {ε δ α : Type} {action : Except ε α} {f : ε → δ} {out : α}
    (h : action.mapError f = .ok out) : action = .ok out := by
  cases action with
  | error error => cases h
  | ok value =>
    cases h
    rfl

private theorem readOne_ok_iff {limit : Nat} {length : Int32} {source rest : List UInt8}
    {value : Bytes} :
    Internal.readOne limit length source = .ok (value, rest) ↔
      length.toInt = (value.length : Int) ∧ value.length ≤ limit ∧
      source = value.toList ++ rest := by
  constructor
  · intro h
    simp only [Internal.readOne] at h
    split at h
    · contradiction
    · rename_i nonnegative
      split at h
      · contradiction
      · rename_i cap
        cases taken : Hybrid.takeExact length.toInt.toNat source with
        | error error => rw [taken] at h; contradiction
        | ok pair =>
          obtain ⟨bytes, suffix⟩ := pair
          rw [taken] at h
          cases h
          obtain ⟨size, wire⟩ := Hybrid.takeExact_ok_iff.mp taken
          refine ⟨?_, ?_, by simpa using wire⟩
          · rw [Bytes.length_ofList, size]
            exact (Int.toNat_of_nonneg (by omega)).symm
          · rw [Bytes.length_ofList, size]
            omega
  · rintro ⟨size, bounded, rfl⟩
    have nonnegative : ¬ length.toInt < 0 := by omega
    have extent : length.toInt.toNat = value.length := by omega
    have read : Hybrid.takeExact value.length (value.toList ++ rest) = .ok (value.toList, rest) :=
      Hybrid.takeExact_ok_iff.mpr ⟨Bytes.length_toList value, rfl⟩
    simp [Internal.readOne, nonnegative, extent, Nat.not_lt_of_ge bounded, read]

private theorem readValues_sound {limit : Nat} {lengths : List Int32} {source : List UInt8}
    {reversed output : List Bytes} (h : Internal.readValues limit lengths source reversed = .ok output) :
    ∃ values, output = reversed.reverse ++ values ∧
      lengths.map Int32.toInt = values.map (fun value => (value.length : Int)) ∧
      source = values.flatMap Bytes.toList ∧ ∀ value ∈ values, value.length ≤ limit := by
  induction lengths generalizing source reversed with
  | nil =>
    cases source with
    | nil =>
      cases h
      exact ⟨[], by simp, rfl, rfl, by simp⟩
    | cons => contradiction
  | cons length lengths ih =>
    unfold Internal.readValues at h
    obtain ⟨⟨value, _⟩, read, h⟩ := bind_ok h
    obtain ⟨vsize, vlimit, vwire⟩ := readOne_ok_iff.mp read
    obtain ⟨rest, order, sizes, wire, bound⟩ := ih h
    refine ⟨value :: rest, ?_, by simp [vsize, sizes], by simp [vwire, wire], ?_⟩
    · simpa [List.reverse_cons, List.append_assoc] using order
    · intro item member
      rcases List.mem_cons.mp member with rfl | later
      · exact vlimit
      · exact bound item later

private theorem readValues_complete {limit : Nat} {lengths : List Int32} {values : List Bytes}
    (sizes : lengths.map Int32.toInt = values.map (fun value => (value.length : Int)))
    (bounded : ∀ value ∈ values, value.length ≤ limit) (reversed : List Bytes) :
    Internal.readValues limit lengths (values.flatMap Bytes.toList) reversed =
      .ok (reversed.reverse ++ values) := by
  induction lengths generalizing values reversed with
  | nil =>
    cases values with
    | nil => simp [Internal.readValues]
    | cons => simp at sizes
  | cons length lengths ih =>
    cases values with
    | nil => simp at sizes
    | cons value values =>
      obtain ⟨size, sizes⟩ := List.cons.inj sizes
      have checked : Internal.readOne limit length (value.toList ++ values.flatMap Bytes.toList) =
          .ok (value, values.flatMap Bytes.toList) :=
        readOne_ok_iff.mpr ⟨size, bounded value (by simp), rfl⟩
      have tail := ih sizes (fun item member => bounded item (List.mem_cons_of_mem _ member))
        (value :: reversed)
      rw [List.flatMap_cons, Internal.readValues, checked]
      change Internal.readValues limit lengths (values.flatMap Bytes.toList) (value :: reversed) = _
      simpa [List.reverse_cons, List.append_assoc] using tail

public theorem assemble_ok_iff {limits : Limits} {lengths : List Int32} {payload : List UInt8}
    {values : List Bytes} :
    assemble limits lengths payload = .ok values ↔ Assembled limits lengths payload values := by
  constructor
  · intro h
    unfold assemble at h
    split at h
    · contradiction
    · rename_i cap
      obtain ⟨_, rfl, sizes, wire, bounded⟩ := readValues_sound h
      exact ⟨Nat.le_of_not_gt cap, sizes, wire, bounded⟩
  · rintro ⟨cap, sizes, wire, bounded⟩
    rw [assemble, ite_eq_right (Nat.not_lt_of_ge cap), wire]
    simpa using readValues_complete sizes bounded []

public theorem decode_sound {limits : Limits} {expected : Nat} {source : Bytes}
    {values : List Bytes} (h : decode limits expected source = .ok values) :
    ∃ (stream : DeltaBinaryPacked.Stream) (payload : List UInt8),
      source.length ≤ limits.lengths.bytes ∧ source.toList = stream.wire ++ payload ∧
      source.length = stream.wire.length + (values.map Bytes.length).sum ∧
      stream.Valid .int32 limits.lengths expected ∧
      Assembled limits (stream.reconstruct .int32) payload values ∧ values.length = expected := by
  unfold decode at h
  obtain ⟨⟨stream, payload⟩, parsed, h⟩ := bind_ok h
  obtain ⟨cap, wire, valid⟩ := DeltaBinaryPacked.parsePrefix_sound (mapError_ok parsed)
  have assembled := assemble_ok_iff.mp h
  refine ⟨stream, payload, cap, wire, ?_, valid, assembled, ?_⟩
  · rw [← Bytes.length_toList, wire, assembled.wire, List.length_append]
    simp [List.length_flatMap]
  · have size := congrArg List.length assembled.sizes
    rw [List.length_map, List.length_map, DeltaBinaryPacked.reconstruct_length valid] at size
    exact size.symm

end Silmaril.Proofs.Formats.Parquet.DeltaLengthByteArray
