module

public import Silmaril.Wasm.Interp.Defs
public import Silmaril.Wasm.Binaryen.NativeProfile

/-!
# The instruction profile of the extended arity check

The F4 adequacy theorems (`Silmaril.Wasm.Interp.OracleX`) are not gated by the native profile
`Binaryen.NativeFuncsOk`. Their gate is the extended store and body check `StoreChkE ext`/`chkE
ext`. `xInstr` lists the flat instructions that `flatChkE ext` can accept, for any extension:
the native profile's instructions (`Binaryen.nativeInstr`), the annotated `select`, and the five
call forms the extension describes. Every other flat instruction (floats, vectors, references,
tables, memory size/grow/bulk, `throw`) is rejected, and so is `try_table` (`chk1E`). Code after
an instruction that never falls through is not checked (it never runs).

Theorems in `Silmaril.Wasm.Interp.XProfile.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp.XProfile

open Silmaril.Wasm

/-- The flat instructions some extended arity check accepts. -/
def xInstr : Instr → Bool
  | .nop | .unreachable | .drop | .select _ | .br _ | .brIf _ | .brTable _ _ | .call _
  | .return_ | .localGet _ | .localSet _ | .localTee _ | .globalGet _ | .globalSet _
  | .intConst _ _ | .intUnOp _ _ | .intBinOp _ _ | .intTestOp _ _ | .intRelOp _ _
  | .intLoad _ none _ _ | .intStore _ none _ _ => true
  | .callIndirect _ _ | .callRef _ | .returnCall _ | .returnCallRef _ | .returnCallIndirect _ _ =>
    true
  | _ => false

/-- The five call forms the extension describes. -/
def xCallForm : Instr → Bool
  | .callIndirect _ _ | .callRef _ | .returnCall _ | .returnCallRef _ | .returnCallIndirect _ _ =>
    true
  | _ => false

end Silmaril.Wasm.Interp.XProfile
