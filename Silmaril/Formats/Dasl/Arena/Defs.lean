module

public import Silmaril.Formats.Dasl.Encode.Defs
public import Silmaril.Formats.Dasl.RawStore.Defs
public import Silmaril.Semantics.Arena.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Arena

open Silmaril.Semantics.Arena

variable {Key Name Source Target Mid : Type} {limit : Nat}

abbrev ShallowState (Key Name : Type) := State Key Name (Shallow Name)

/-- The existing name (or its absence) is an input, never an output. -/
abbrev Codec (Name Source Target : Type) := Option Name → Encode.PartialCodec Source Target

abbrev Converter (Name Source Target : Type) := Option Name → Source → Option Target

def Codec.lift (codec : Encode.PartialCodec Source Target) : Codec Name Source Target := fun _ => codec

def Codec.encode (codec : Codec Name Source Target) : Converter Name Source Target := fun name => (codec name).encode?

def Codec.decode (codec : Codec Name Source Target) : Converter Name Target Source := fun name => (codec name).decode?

def Codec.then (first : Codec Name Source Mid) (second : Codec Name Mid Target) : Codec Name Source Target :=
  fun name => (first name).then (second name)

namespace Converter

/-- A failure is a resident payload that the converter rejects, not a hole or reservation. -/
def rejected (convert : Converter Name Source Target) : Option (Slot Name Source) → Bool
  | some ⟨name, some payload⟩ => (convert name payload).isNone
  | _ => false

/-- Lossy snapshot: rejection discards only the local payload. Use `rejected` to observe the loss. -/
def discardCell (convert : Converter Name Source Target) : Option (Slot Name Source) → Option (Slot Name Target) :=
  Option.map fun slot => ⟨slot.name, slot.payload.bind (convert slot.name)⟩

def strictCell (convert : Converter Name Source Target) (cell : Option (Slot Name Source)) :
    Except Unit (Option (Slot Name Target)) :=
  if convert.rejected cell then .error () else .ok (convert.discardCell cell)

def discard (convert : Converter Name Source Target) (arena : State Key Name Source) : State Key Name Target :=
  fun key => convert.discardCell (arena key)

def discardDense (convert : Converter Name Source Target) (arena : Dense limit Name Source) : Dense limit Name Target :=
  ⟨Array.ofFn (fun index : Fin limit => convert.discardCell (arena.read index)), Array.size_ofFn⟩

/-- Strict finite conversion reports a rejecting index in increasing order. No partial output escapes. -/
def strictDense (convert : Converter Name Source Target) (arena : Dense limit Name Source) :
    Except (Fin limit) (Dense limit Name Target) :=
  match (List.finRange limit).find? (fun index : Fin limit => convert.rejected (arena.read index)) with
  | some index => .error index
  | none => .ok (convert.discardDense arena)

end Converter

namespace Codec

/-- The image of actual resident, named observations under successful encoding.
Decoder acceptance by itself does not place bytes in this image. -/
def image (codec : Codec Name Source Target) (source : Semantics.Naming.Relation Name Source) :
    Semantics.Naming.Relation Name Target :=
  fun name target => ∃ payload, source name payload ∧ codec.encode (some name) payload = some target

end Codec

end Silmaril.Formats.Dasl.Arena
