module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Defs
public import Silmaril.Wasm.V1.Execution.Step

/-!
# Native WebAssembly 1.0 indirect resolution

Lookup uses table slot zero and reads the unsigned i32 selector before consulting
the declaration. An absent table, or an initialized slot with a missing type
or function, has no native successor. A bounds or uninitialized-entry trap
requires only the allocated table.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect

open Execution.Runtime (Frame FuncAddr TableInst Value)
open Wasm.V1.Execution

/-- Read the entry before the type. Both the native store and a checked
allocation use this lookup with their own function-type projection. -/
def resolveTable (table : TableInst) (expected : Option Wasm.V1.FuncType)
    (funType : FuncAddr → Option Wasm.V1.FuncType) (selector : BitVec 32) : Option Outcome :=
  match table.refs[selector.toNat]? with
  | none => some .bounds
  | some none => some .null
  | some (some address) => do
    let signature ← expected
    let actual ← funType address
    return if actual = signature then .resolved address else .mismatch address

/-- Resolve the leading native indirect site using its live allocation. -/
def v1Resolve {H : Type} (s : Store H) (caller : Frame) (index : TypeIdx) (selector : BitVec 32) :
    Option Outcome := do
  let table ← frameTable s caller
  resolveTable table caller.module.types[index.toNat]? (fun a => s.funcs[a.value]?.map (·.type)) selector

def v1Source {H : Type} (s : Store H) (caller : Frame) (index : TypeIdx) (selector : BitVec 32)
    (stack : List Value) (tail : List Admin) : Config H :=
  ⟨s, caller, values (stack ++ [Value.int .i32 selector]) ++ .source (.callIndirect index) :: tail⟩

def Outcome.v1Head : Outcome → Admin
  | .resolved address => .invoke address
  | _ => .trap

def v1Resolved {H : Type} (s : Store H) (caller : Frame) (stack : List Value) (tail : List Admin)
    (out : Outcome) : Config H :=
  ⟨s, caller, values stack ++ out.v1Head :: tail⟩

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect
