module

public import Silmaril.Formats.Parquet.ScalarPage.Defs
import Silmaril.Proofs.Formats.Parquet.ScalarPage.Prepare
import Silmaril.Formats.Parquet.Plain.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.ScalarPage

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.ScalarPage

private theorem flatten_length {width : Nat} {words : List (List UInt8)}
    (sized : ∀ word ∈ words, word.length = width) :
    words.flatten.length = words.length * width := by
  induction words with
  | nil => simp
  | cons word rest ih =>
    have hw := sized word (by simp)
    have hr : ∀ w ∈ rest, List.length w = width := fun w h => sized w (by simp [h])
    simp [hw, ih hr, Nat.succ_mul, Nat.add_comm]

private theorem fixed_size {α : Type} {width count : Nat} {one : List UInt8 → α}
    {source : Bytes} {values : List α}
    (h : Plain.decodeFixedWidth width count one source = .ok values) :
    source.length = count * width := by
  obtain ⟨_, words, bytes, rfl, sized, _⟩ := Plain.decodeFixedWidth_ok_iff.mp h
  rw [← Bytes.length_toList, bytes, flatten_length sized]

public theorem readPlain_size {kind : Kind} {count : Nat} {source : Bytes}
    {values : List kind.Value} (h : kind.readPlain count source = .ok values) :
    source.length = kind.plainByteCount count := by
  cases kind with
  | int32 => exact fixed_size h
  | int64 => exact fixed_size h
  | boolean => exact (Plain.decodeBoolean_ok_iff.mp h).1
  | floatBits => exact fixed_size h
  | doubleBits => exact fixed_size h
  | fixedLenBytes width =>
    change Plain.decodeFixedLenBytes width count source = .ok values at h
    unfold Plain.decodeFixedLenBytes at h
    split at h
    · exact fixed_size h
    · contradiction

public theorem decode_sound {kind : Kind} {params : Parameters} {limits : Limits} {source : Bytes}
    {output : List (Option kind.Value)} (h : decode kind params limits source = .ok output) :
    ∃ page values, prepare params limits source = .ok page ∧
      kind.readPlain (page.mask.count true) page.scalars = .ok values ∧
      output.map Option.isSome = page.mask ∧ output.filterMap id = values ∧
      values.length = page.mask.count true ∧
      page.scalars.length = kind.plainByteCount (page.mask.count true) := by
  obtain ⟨page, hp, h⟩ := bind_ok h
  obtain ⟨values, hv, h⟩ := bind_ok h
  have plain := mapError_ok hv
  have reconstructed := mapError_ok h
  obtain ⟨shape, order⟩ := FlatPage.reconstruct_ok_iff.mp reconstructed
  have count := (FlatPage.reconstruct_exists_iff page.mask values).mp ⟨output, reconstructed⟩
  exact ⟨page, values, hp, plain, shape, order, count.symm, readPlain_size plain⟩

public theorem decode_counts {kind : Kind} {params : Parameters} {limits : Limits} {source : Bytes}
    {output : List (Option kind.Value)} (h : decode kind params limits source = .ok output) :
    output.length = params.numValues ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => (output.filterMap id).length = params.numValues - nulls := by
  obtain ⟨page, values, hp, _, shape, order, size, _⟩ := decode_sound h
  refine ⟨?_, ?_⟩
  · have lengths := congrArg List.length shape
    rwa [List.length_map, prepared_mask_length hp] at lengths
  · cases version : params.version with
    | v1 => trivial
    | v2 =>
      obtain ⟨_, _, wire⟩ := prepare_sound hp
      simp only [PreparedWire, version] at wire
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, count, _⟩ := wire
      rw [order, size, count]

end Silmaril.Proofs.Formats.Parquet.ScalarPage
