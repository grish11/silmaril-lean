module

public import Silmaril.Formats.Parquet.DeltaByteArray.Defs
import Silmaril.Formats.Parquet.DeltaBinaryPacked.Thms
import Silmaril.Formats.Parquet.DeltaLengthByteArray.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.DeltaByteArray

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.DeltaByteArray

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

private theorem checkSize_ok_iff {limit budget prefixBytes suffixBytes : Nat} :
    Internal.checkSize limit budget prefixBytes suffixBytes = .ok () ↔
      prefixBytes + suffixBytes < valueLengthLimit ∧ prefixBytes + suffixBytes ≤ limit ∧
      prefixBytes + suffixBytes ≤ budget := by
  constructor
  · intro h
    simp only [Internal.checkSize] at h
    split at h
    · contradiction
    · rename_i representable
      split at h
      · contradiction
      · rename_i cap
        split at h
        · contradiction
        · exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨representable, cap, fits⟩
    simp [Internal.checkSize, Nat.not_le_of_lt representable, Nat.not_lt_of_ge cap,
      Nat.not_lt_of_ge fits]

private theorem joined_length {previous suffix value : Bytes} {count : Nat}
    (fits : count ≤ previous.length)
    (wire : value.toList = previous.toList.take count ++ suffix.toList) :
    value.length = count + suffix.length := by
  simpa only [List.length_append, List.length_take, Bytes.length_toList, Nat.min_eq_left fits] using
    congrArg List.length wire

private theorem extend_ok_iff {limit budget : Nat} {previous suffix value : Bytes} {prefixLength : Int32} :
    Internal.extend limit budget previous prefixLength suffix = .ok value ↔
      Joined limit budget previous prefixLength suffix value := by
  constructor
  · intro h
    simp only [Internal.extend] at h
    split at h
    · contradiction
    · rename_i nonnegative
      split at h
      · contradiction
      · rename_i bound
        obtain ⟨validated, checked, h⟩ := bind_ok h
        cases validated
        obtain ⟨width, cap, fits⟩ := checkSize_ok_iff.mp checked
        cases h
        have prefixFits : prefixLength.toInt.toNat ≤ previous.length := by omega
        have bytes := Bytes.toList_ofList (previous.toList.take prefixLength.toInt.toNat ++ suffix.toList)
        have size := joined_length prefixFits bytes
        exact ⟨by omega, prefixFits, bytes, size.symm ▸ width, size.symm ▸ cap, size.symm ▸ fits⟩
  · intro joined
    have size := joined_length joined.prefixFits joined.wire
    have checked : Internal.checkSize limit budget prefixLength.toInt.toNat suffix.length = .ok () :=
      checkSize_ok_iff.mpr ⟨size ▸ joined.representable, size ▸ joined.limit, size ▸ joined.budgetFits⟩
    have bytes : Bytes.ofList (previous.toList.take prefixLength.toInt.toNat ++ suffix.toList) = value :=
      Bytes.ext (by simpa using joined.wire.symm)
    rw [Internal.extend, ite_eq_right (Int.not_lt_of_ge joined.nonnegative)]
    dsimp only
    rw [ite_eq_right (Nat.not_lt_of_ge joined.prefixFits), checked]
    exact congrArg Except.ok bytes

private theorem loop_sound {limit budget : Nat} {previous : Bytes}
    {prefixes : List Int32} {suffixes reversed output : List Bytes}
    (h : Internal.loop limit budget previous prefixes suffixes reversed = .ok output) :
    ∃ values, output = reversed.reverse ++ values ∧
      Reconstruction limit budget previous prefixes suffixes values := by
  induction prefixes generalizing budget previous suffixes reversed with
  | nil =>
    cases suffixes with
    | nil =>
      cases h
      exact ⟨[], by simp, .done ..⟩
    | cons => contradiction
  | cons prefixLength prefixes ih =>
    cases suffixes with
    | nil => contradiction
    | cons suffix suffixes =>
      unfold Internal.loop at h
      obtain ⟨value, joined, h⟩ := bind_ok h
      obtain ⟨values, order, tail⟩ := ih h
      exact ⟨value :: values, by simpa [List.reverse_cons, List.append_assoc] using order,
        .next (extend_ok_iff.mp joined) tail⟩

private theorem loop_complete {limit budget : Nat} {previous : Bytes}
    {prefixes : List Int32} {suffixes values : List Bytes}
    (reconstruction : Reconstruction limit budget previous prefixes suffixes values)
    (reversed : List Bytes) :
    Internal.loop limit budget previous prefixes suffixes reversed = .ok (reversed.reverse ++ values) := by
  induction reconstruction generalizing reversed with
  | done => simp [Internal.loop]
  | @next budget previous suffix value prefixLength prefixes suffixes values joined tail ih =>
    rw [Internal.loop, extend_ok_iff.mpr joined]
    change Internal.loop limit (budget - value.length) value prefixes suffixes (value :: reversed) = _
    simpa [List.reverse_cons, List.append_assoc] using ih (value :: reversed)

public theorem reconstruct_ok_iff {limits : Limits} {prefixes : List Int32} {suffixes values : List Bytes} :
    reconstruct limits prefixes suffixes = .ok values ↔ prefixes.headD 0 = 0 ∧
      Reconstruction limits.valueBytes limits.decodedBytes .empty prefixes suffixes values := by
  constructor
  · intro h
    unfold reconstruct at h
    split at h
    · contradiction
    · rename_i first
      obtain ⟨values, rfl, reconstruction⟩ := loop_sound h
      exact ⟨not_not.mp first, reconstruction⟩
  · rintro ⟨first, reconstruction⟩
    have checked : ¬ prefixes.headD 0 ≠ 0 := fun rejects => rejects first
    rw [reconstruct, ite_eq_right checked]
    simpa using loop_complete reconstruction []

public theorem reconstruction_sizes {limit budget : Nat} {previous : Bytes}
    {prefixes : List Int32} {suffixes values : List Bytes}
    (h : Reconstruction limit budget previous prefixes suffixes values) :
    values.length = prefixes.length ∧ values.length = suffixes.length ∧
      (values.map Bytes.length).sum ≤ budget := by
  induction h with
  | done => simp
  | next joined _ ih =>
    obtain ⟨prefixesLength, suffixesLength, total⟩ := ih
    refine ⟨by simp [prefixesLength], by simp [suffixesLength], ?_⟩
    simp only [List.map_cons, List.sum_cons]
    have budget := joined.budgetFits
    omega

public theorem decode_sound {limits : Limits} {expected : Nat} {source : Bytes}
    {values : List Bytes} (h : decode limits expected source = .ok values) :
    ∃ (prefixStream suffixStream : DeltaBinaryPacked.Stream) (payload : List UInt8)
        (suffixes : List Bytes),
      source.length ≤ limits.prefixes.bytes ∧
      source.toList = prefixStream.wire ++ suffixStream.wire ++ payload ∧
      source.length = prefixStream.wire.length + suffixStream.wire.length + (suffixes.map Bytes.length).sum ∧
      prefixStream.Valid .int32 limits.prefixes expected ∧
      suffixStream.Valid .int32 limits.suffixes.lengths expected ∧
      DeltaLengthByteArray.Assembled limits.suffixes (suffixStream.reconstruct .int32) payload suffixes ∧
      (prefixStream.reconstruct .int32).headD 0 = 0 ∧
      Reconstruction limits.valueBytes limits.decodedBytes .empty
        (prefixStream.reconstruct .int32) suffixes values ∧
      values.length = expected ∧ (values.map Bytes.length).sum ≤ limits.decodedBytes := by
  unfold decode at h
  obtain ⟨⟨prefixStream, suffixSource⟩, prefixRead, h⟩ := bind_ok h
  obtain ⟨suffixes, suffixRead, h⟩ := bind_ok h
  obtain ⟨prefixCap, prefixWire, prefixValid⟩ := DeltaBinaryPacked.parsePrefix_sound (mapError_ok prefixRead)
  obtain ⟨suffixStream, payload, _, rawSuffixWire, suffixSize, suffixValid, suffixAssembly, suffixCount⟩ :=
    DeltaLengthByteArray.decode_sound (mapError_ok suffixRead)
  obtain ⟨first, reconstruction⟩ := reconstruct_ok_iff.mp h
  obtain ⟨_, count, total⟩ := reconstruction_sizes reconstruction
  refine ⟨prefixStream, suffixStream, payload, suffixes, prefixCap, ?_, ?_, prefixValid,
    suffixValid, suffixAssembly, first, reconstruction, count.trans suffixCount, total⟩
  · have suffixWire : suffixSource = suffixStream.wire ++ payload := by
      simpa only [Bytes.toList_ofList] using rawSuffixWire
    rw [prefixWire, suffixWire, List.append_assoc]
  · rw [← Bytes.length_toList, prefixWire, List.length_append]
    rw [Bytes.length_ofList] at suffixSize
    omega

end Silmaril.Proofs.Formats.Parquet.DeltaByteArray
