module

public import Silmaril.Formats.Dasl.Arena.Defs
public import Silmaril.Semantics.Arena.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.Arena

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Arena Silmaril.Semantics.Arena
open Silmaril.Semantics.Naming

variable {Key Name Source Target : Type} {limit : Nat}

theorem strictDense_ok_iff (convert : Converter Name Source Target) (arena : Dense limit Name Source)
    (next : Dense limit Name Target) : convert.strictDense arena = .ok next ↔
      (∀ index : Fin limit, convert.rejected (arena.read index) = false) ∧ next = convert.discardDense arena := by
  simp only [Converter.strictDense]
  have noReject : (List.finRange limit).find? (fun index : Fin limit => convert.rejected (arena.read index)) = none ↔
      ∀ index : Fin limit, convert.rejected (arena.read index) = false := by
    simp [List.find?_eq_none, List.mem_finRange]
  split
  · rename_i index hit
    rw [← noReject, hit]
    simp
  · rename_i hit
    simp [noReject.mp hit, eq_comm]

theorem strictDense_error (convert : Converter Name Source Target) (arena : Dense limit Name Source)
    {index : Fin limit} (failed : convert.strictDense arena = .error index) :
    convert.rejected (arena.read index) = true := by
  unfold Converter.strictDense at failed
  split at failed
  · rename_i found hit
    cases failed
    have rejected := List.find?_some hit
    exact rejected
  · contradiction

theorem encode_discard_observations (codec : Codec Name Source Target) (arena : State Key Name Source) :
    (codec.encode.discard arena).observations = codec.image arena.observations := by
  funext name target
  apply propext
  constructor
  · rintro ⟨key, hit⟩
    cases observed : arena key with
    | none => simp [Converter.discard, Converter.discardCell, observed] at hit
    | some slot =>
      obtain ⟨oldName, payload⟩ := slot
      cases payload with
      | none => simp [Converter.discard, Converter.discardCell, observed] at hit
      | some payload =>
        simp [Converter.discard, Converter.discardCell, observed] at hit
        exact ⟨payload, ⟨key, by simpa [hit.1] using observed⟩, by simpa [hit.1] using hit.2⟩
  · rintro ⟨payload, ⟨key, observed⟩, encoded⟩
    exact ⟨key, by simp [Converter.discard, Converter.discardCell, observed, encoded]⟩

theorem decode_encode_discardCell (codec : Codec Name Source Target) (cell : Option (Slot Name Source))
    (accepted : codec.encode.rejected cell = false) : codec.decode.discardCell (codec.encode.discardCell cell) = cell := by
  rcases cell with _ | ⟨name, _ | payload⟩
  · rfl
  · rfl
  · cases encoded : (codec name).encode? payload with
    | none => simp [Converter.rejected, Codec.encode, encoded] at accepted
    | some target => simp [Converter.discardCell, Codec.encode, Codec.decode, encoded, (codec name).recovers encoded]

theorem raw_discard_observations (decoder : RawStore.Decoder Name) (arena : ByteState Key Name) :
    ∀ name shallow, (decoder.view arena.observations).objects name shallow ↔ decoder.objectName name ∧
      (Converter.discard (fun _ => decoder.parse?) arena).observations name shallow := by
  intro name shallow
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨bytes, ⟨key, hit⟩, parsed⟩
    exact ⟨key, by simp [Converter.discard, Converter.discardCell, hit, parsed]⟩
  · rintro ⟨key, hit⟩
    rcases read : arena key with _ | ⟨oldName, _ | bytes⟩
    · simp [Converter.discard, Converter.discardCell, read] at hit
    · simp [Converter.discard, Converter.discardCell, read] at hit
    · simp [Converter.discard, Converter.discardCell, read] at hit
      exact ⟨bytes, ⟨key, by simpa [hit.1] using read⟩, hit.2⟩

end Silmaril.Proofs.Formats.Dasl.Arena
