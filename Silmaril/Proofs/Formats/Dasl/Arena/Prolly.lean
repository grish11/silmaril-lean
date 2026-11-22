module

public import Silmaril.Formats.Dasl.Arena.Prolly.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.Arena.Prolly

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Arena.Prolly
open Silmaril.Formats.Dasl.Prolly (Read readBlock)
open Silmaril.Semantics.Naming

variable {Name Key Payload : Type}

theorem readRaw_sound (decoder : RawStore.Decoder Name) [DecidablePred decoder.objectName]
    {fetch : Name → Option ByteArray} {raw : RawStore.Blocks Name}
    (sound : ∀ ⦃name bytes⦄, fetch name = some bytes → raw name bytes) :
    Read.Sound (readRaw decoder fetch) (decoder.view raw) := by
  intro name value found
  unfold readRaw at found
  split at found
  · rename_i object
    split at found
    · contradiction
    · rename_i bytes fetched
      split at found
      · contradiction
      · rename_i parsed decoded
        cases found
        exact ⟨object, bytes, sound fetched, decoded⟩
  · contradiction

theorem read_capture [DecidableEq Name] (codec : BlockCodec Name Key Payload) (input : Read Name) (names : List Name) :
    (Resident.capture codec input names).read = readBlock codec (restrict input names) := by
  funext name
  have exactRead : ((names.map fun item => (item, readBlock codec input item)).lookup name) =
      if name ∈ names then some (readBlock codec input name) else none := by
    induction names with
    | nil => rfl
    | cons item tail ih =>
      by_cases same : name = item
      · subst item
        simp
      · simp [List.lookup, same, beq_eq_false_iff_ne.mpr same, ih]
  unfold Resident.capture Resident.read
  rw [exactRead]
  by_cases acquired : name ∈ names <;> simp [restrict, acquired, readBlock]

end Silmaril.Proofs.Formats.Dasl.Arena.Prolly
