module

public import Silmaril.Formats.Dasl.Arena.Defs
public import Silmaril.Semantics.Arena.Thms
import Silmaril.Proofs.Formats.Dasl.Arena.Codec

public section

namespace Silmaril.Formats.Dasl.Arena

open Silmaril.Semantics.Arena Silmaril.Semantics.Naming

variable {Key Name Source Target : Type} {limit : Nat}

namespace Converter

@[simp] theorem occupancy (convert : Converter Name Source Target) (cell : Option (Slot Name Source)) :
    (convert.discardCell cell).isSome = cell.isSome := by cases cell <;> rfl

@[simp] theorem retainedName (convert : Converter Name Source Target) (cell : Option (Slot Name Source)) :
    (convert.discardCell cell).map Slot.name = cell.map Slot.name := by cases cell <;> rfl

theorem strictCell_ok_iff (convert : Converter Name Source Target) (cell : Option (Slot Name Source))
    (next : Option (Slot Name Target)) : convert.strictCell cell = .ok next ↔
      convert.rejected cell = false ∧ next = convert.discardCell cell := by
  cases rejected : convert.rejected cell <;> simp [strictCell, rejected, eq_comm]

@[simp] theorem discardDense_read (convert : Converter Name Source Target) (arena : Dense limit Name Source)
    (index : Fin limit) : (convert.discardDense arena).read index = convert.discardCell (arena.read index) :=
  Dense.read_ofFn _ index

theorem strictDense_ok_iff (convert : Converter Name Source Target) (arena : Dense limit Name Source)
    (next : Dense limit Name Target) : convert.strictDense arena = .ok next ↔
      (∀ index : Fin limit, convert.rejected (arena.read index) = false) ∧ next = convert.discardDense arena :=
  Proofs.Formats.Dasl.Arena.strictDense_ok_iff convert arena next

theorem strictDense_error (convert : Converter Name Source Target) (arena : Dense limit Name Source)
    {index : Fin limit} (failed : convert.strictDense arena = .error index) :
    convert.rejected (arena.read index) = true :=
  Proofs.Formats.Dasl.Arena.strictDense_error convert arena failed

end Converter

namespace Codec

theorem image_lift (codec : Encode.PartialCodec Source Target) (reference : Relation Name Source) :
    (lift codec).image reference = push reference (fun source target => codec.encode? source = some target) := rfl

theorem image_binding (codec : Codec Name Source Target) {reference : Relation Name Source}
    (bound : Binding reference) : Binding (codec.image reference) := by
  rintro name left right ⟨source, present, encoded⟩ ⟨other, alsoPresent, alsoEncoded⟩
  rw [← bound present alsoPresent, encoded] at alsoEncoded
  exact Option.some.inj alsoEncoded

theorem encode_discard_observations (codec : Codec Name Source Target) (arena : State Key Name Source) :
    (codec.encode.discard arena).observations = codec.image arena.observations :=
  Proofs.Formats.Dasl.Arena.encode_discard_observations codec arena

/-- A representation change preserves admitted bindings only with the relevant reference bridge.
In particular encoding success is not evidence that the retained name is a hash of the result. -/
theorem encode_discard_admitted (codec : Codec Name Source Target) {arena : State Key Name Source}
    {source : Relation Name Source} {target : Relation Name Target} (admitted : arena.AdmittedBy source)
    (bridge : Subset (codec.image source) target) : (codec.encode.discard arena).AdmittedBy target := by
  show Subset (codec.encode.discard arena).observations target
  rw [codec.encode_discard_observations]
  rintro name repr ⟨payload, hit, encoded⟩; exact bridge ⟨payload, admitted hit, encoded⟩

theorem decode_encode_discardCell (codec : Codec Name Source Target) (cell : Option (Slot Name Source))
    (accepted : codec.encode.rejected cell = false) : codec.decode.discardCell (codec.encode.discardCell cell) = cell :=
  Proofs.Formats.Dasl.Arena.decode_encode_discardCell codec cell accepted

theorem decode_encode_discard (codec : Codec Name Source Target) (arena : State Key Name Source)
    (accepted : ∀ key, codec.encode.rejected (arena key) = false) : codec.decode.discard (codec.encode.discard arena) = arena :=
  funext fun key => codec.decode_encode_discardCell (arena key) (accepted key)

end Codec

/-- The existing raw-store decoder interprets only the object lane. Arena conversion on its
own does not impose the name-domain check, nor does it verify integrity of the original bytes. -/
theorem raw_discard_observations (decoder : RawStore.Decoder Name) (arena : ByteState Key Name) :
    ∀ name shallow, (decoder.view arena.observations).objects name shallow ↔ decoder.objectName name ∧
      (Converter.discard (fun _ => decoder.parse?) arena).observations name shallow :=
  Proofs.Formats.Dasl.Arena.raw_discard_observations decoder arena

end Silmaril.Formats.Dasl.Arena
