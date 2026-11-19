module

public import Silmaril.Wasm.Region.ByteMap.Equality.Defs
import Silmaril.Proofs.Wasm.Region.ByteMapEquality

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.Equality

theorem equal_iff (a b : Instr) : equal a b = true ↔ a = b := Proofs.equal_iff a b

instance : DecidableEq Instr := fun a b => decidable_of_iff (equal a b = true) (equal_iff a b)

end Silmaril.Wasm.Region.ByteMap.Equality
