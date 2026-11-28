module

public import Silmaril.Wasm.Lime1.Execution.Step

/-!
# Indexed loop admission at an active Lime1 frame

Entry and restart use the same ordered parameter signature. Completion uses
the distinct result signature. Native control accepts opaque host bodies and
does not itself check operand types.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Loops

open Execution.Runtime (Frame Value)

structure LimeIndexedLoop where
  index : TypeIdx
  signature : Wasm.Lime1.FuncType
  body : Wasm.Lime1.Expr

namespace LimeIndexedLoop

def instr (loop : LimeIndexedLoop) : Wasm.Lime1.Instr :=
  .loop (.typeIdx loop.index) loop.body

def Resolved (loop : LimeIndexedLoop) (frame : Frame) : Prop :=
  frame.module.types[loop.index.toNat]? = some loop.signature

def Parameters (loop : LimeIndexedLoop) (operands : List Value) : Prop :=
  operands.map Value.type = loop.signature.params

def Results (loop : LimeIndexedLoop) (operands : List Value) : Prop :=
  operands.map Value.type = loop.signature.results

end LimeIndexedLoop
end Silmaril.Wasm.Institution.Operational.Loops
