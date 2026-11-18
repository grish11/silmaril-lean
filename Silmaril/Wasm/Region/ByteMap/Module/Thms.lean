module

public import Silmaril.Wasm.Region.ByteMap.Module.Defs
public import Silmaril.Wasm.Region.ByteMap.Thms
import Silmaril.Proofs.Wasm.Region.ByteMapModule

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.ModuleSource
open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

theorem Certified.body_checks {raw : List UInt8} (source : Certified raw)
    (i : Fin source.layout.bodies.length) :
    (source.layout.bodies[i]).Checks raw source.decoded source.layout i.val := source.checked.2.2.2.2.2.2 i

theorem Certified.body_bytes {raw : List UInt8} (source : Certified raw)
    (i : Fin source.layout.bodies.length) :
    (raw.drop (source.layout.bodyStart i.val)).take (source.layout.bodies[i]).input.bytes.length =
      (source.layout.bodies[i]).input.bytes := (source.body_checks i).2.2.2.2.2

theorem Certified.function_index {raw : List UInt8} (source : Certified raw)
    (i : Fin source.layout.bodies.length) :
    (source.layout.bodies[i]).input.functionIndex = source.decoded.importedFunctions.length + i.val :=
  (source.body_checks i).2.2.1

theorem Certified.function_body {raw : List UInt8} (source : Certified raw)
    (i : Fin source.layout.bodies.length) :
    (source.decoded.funcs[i.val]?).map functionBody =
      some ((source.layout.bodies[i]).input.localGroups.flatMap expandLocal,
        (source.layout.bodies[i]).input.body) := (source.body_checks i).2.2.2.1

/-- The source-framed code section encodes exactly the defined bodies, in order;
its function indices are adjusted by function imports, never by all imports. -/
theorem Certified.code_encoding {raw : List UInt8} (source : Certified raw) :
    ∃ s ∈ source.layout.code?.toList, s.id = 10 ∧
      Vec (Code Forms.all) s.payload (source.decoded.funcs.map functionBody) := by
  obtain ⟨s, member, id, _, parsed⟩ := source.checked.2.2.2.1
  exact ⟨s, member, id, parseAll_sound (Decode.readVec_sound Decode.readCode_sound) parsed⟩

theorem Certified.index_bound {raw : List UInt8} (source : Certified raw)
    (i : Fin source.layout.bodies.length) :
    (source.layout.bodies[i]).input.functionIndex < source.decoded.functionTypes.length := by
  rw [source.function_index i, Silmaril.Wasm.Module.functionTypes_length]
  exact Nat.add_lt_add_left (source.checked.2.2.2.2.2.1 ▸ i.isLt) _

/-- The selected section is a complete Core code-section grammar witness,
anchored in the exact source framing, rather than an isolated body parse. -/
theorem Certified.code_section {raw : List UInt8} (source : Certified raw) :
    ∃ s ∈ source.layout.code?.toList,
      CodeSec Forms.all s.encoded (source.decoded.funcs.map functionBody) := Proofs.code_section source

theorem Certified.source_framing {raw : List UInt8} (source : Certified raw) :
    raw = magic ++ version ++ source.layout.sections.flatMap Section.encoded := source.checked.1

end Silmaril.Wasm.Region.ByteMap.ModuleSource
