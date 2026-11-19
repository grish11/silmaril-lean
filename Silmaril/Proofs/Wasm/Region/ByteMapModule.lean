module

public import Silmaril.Wasm.Region.ByteMap.Module.Defs
public import Silmaril.Wasm.Region.ByteMap.Thms

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.ModuleSource.Proofs
open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

theorem code_section {raw : List UInt8} (source : Certified raw) :
    ∃ s ∈ source.layout.code?.toList,
      CodeSec Forms.all s.encoded (source.decoded.funcs.map functionBody) := by
  obtain ⟨s, member, id, _, parsed⟩ := source.checked.2.2.2.1
  have lookup : source.layout.sections[source.layout.codeSection]? = some s :=
    Option.mem_toList.mp member
  have size := source.checked.2.1 s (List.mem_of_getElem? lookup)
  have encoded := parseAll_sound (Decode.readVec_sound Decode.readCode_sound) parsed
  refine ⟨s, member, ?_⟩
  change Silmaril.Wasm.Binary.Section 10 _ ([s.id] ++ s.sizeBytes ++ s.payload) _
  rw [id]
  exact .mk (parseAll_sound (Decode.readU_sound 32) size) rfl encoded

end Silmaril.Wasm.Region.ByteMap.ModuleSource.Proofs
