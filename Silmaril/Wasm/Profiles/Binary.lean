module

public import Silmaril.Wasm.Profiles.Thms
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.SpecTec.BinaryAgree.Thms

@[expose] public section

namespace Silmaril.Wasm.Profiles

/-- The binary relation need not have an executable or total codec. -/
class HasEncoding (W : Type) [HasSyntax W] where
  encodes : List UInt8 → Module W → Prop

instance : HasEncoding Wasm1 := ⟨V1.Binary.Encodes⟩
instance : HasEncoding Wasm3 := ⟨Binary.Core.Encodes⟩
instance : HasEncoding Lime := ⟨Lime1.Binary.Encodes⟩
instance : HasEncoding Strict := ⟨fun bytes mod => Binary.Core.Encodes bytes mod.val⟩

/-- Restrict the result of the actual Core decoder, without a second parser. -/
def Strict.decode? (bytes : ByteArray) : Option (Module Strict) := Binary.Core.decode? bytes >>= check?

theorem Strict.decode?_iff {bytes : ByteArray} {mod : Module Strict} :
    decode? bytes = some mod ↔ Binary.Core.decode? bytes = some mod.val := by
  change (Binary.Core.decode? bytes).bind check? = some mod ↔ _
  rw [Option.bind_eq_some_iff]
  exact ⟨fun ⟨_, read, accepted⟩ => check?_sound accepted ▸ read, fun read => ⟨_, read, check?_complete mod⟩⟩

theorem Strict.decode?_sound {bytes : ByteArray} {mod : Module Strict} (decoded : decode? bytes = some mod) :
    HasEncoding.encodes (W := Strict) bytes.data.toList mod := Binary.Core.decode?_sound (decode?_iff.mp decoded)

end Silmaril.Wasm.Profiles
