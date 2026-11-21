module

public import Silmaril.Formats.Dasl.Prolly.Defs
public import Silmaril.Semantics.Prolly.Thms
import Silmaril.Proofs.Formats.Dasl.Prolly

public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics.Prolly

variable {Name Key Payload : Type}

def blockCodec (key : Encode.TotalCodec Key (Shallow Name)) (payload : Encode.TotalCodec Payload (Shallow Name)) :
    Encode.PartialCodec (Block Name Key Payload) (Shallow Name) :=
  ⟨encodeBlock key payload, decodeBlock key payload, fun _ _ => Proofs.Formats.Dasl.Prolly.block_roundtrip key payload⟩

theorem blockCodec_encode (key : Encode.TotalCodec Key (Shallow Name)) (payload : Encode.TotalCodec Payload (Shallow Name)) :
    (blockCodec key payload).encode? = encodeBlock key payload := by unfold blockCodec; rfl

theorem Stored.mono {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    {address : Block Name Key Payload → Name} {tree : Semantics.Prolly.Tree Key Payload} {store extension : Store Name}
    (stored : Stored codec address tree store) (incl : store.Subset extension) : Stored codec address tree extension := by
  intro block hit
  obtain ⟨value, rendered, present⟩ := stored block hit
  exact ⟨value, rendered, incl.1 present⟩

theorem Stored.read_block {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    {address : Block Name Key Payload → Name} {tree : Semantics.Prolly.Tree Key Payload} {store : Store Name}
    (stored : Stored codec address tree store) (bound : store.Binding) {block : Block Name Key Payload}
    (hit : block ∈ blockOccurrences address tree.level tree.root) {value : Shallow Name}
    (read : store.objects (address block) value) : codec.decode? value = some block := by
  obtain ⟨_, rendered, present⟩ := stored block hit
  exact (bound.1 present read) ▸ codec.recovers rendered

end Silmaril.Formats.Dasl.Prolly
