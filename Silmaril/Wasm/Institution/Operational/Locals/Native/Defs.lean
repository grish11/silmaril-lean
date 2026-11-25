module

public import Silmaril.Wasm.Institution.Operational.Locals.Thms
public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Core.Defs
public import Silmaril.Wasm.V1.Execution.Step
public import Silmaril.Wasm.V1.ToCore.Instructions
public import Silmaril.Wasm.Lime1.Execution.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Locals

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (AdminInstr Value)

def coreInstr : Op → Instr
  | .value ⟨.int t, x⟩ => .intConst t x
  | .value ⟨.float t, x⟩ => .floatConst t x
  | .get i => .localGet i
  | .set i => .localSet i
  | .tee i => .localTee i

def readInstr : Instr → Option Op
  | .intConst t x => some (.value (.int t x))
  | .floatConst t x => some (.value (.float t x))
  | .localGet i => some (.get i)
  | .localSet i => some (.set i)
  | .localTee i => some (.tee i)
  | _ => none

theorem readInstr_emit (op : Op) : readInstr (coreInstr op) = some op := by
  cases op with
  | value v => rcases v with ⟨t, x⟩; cases t <;> rfl
  | _ => rfl

theorem readInstr_sound {i : Instr} {op : Op} (h : readInstr i = some op) :
    coreInstr op = i := by cases i <;> cases h <;> rfl

def legacyRead {I : Type} (toCore : I → Instr) : AdminInstr I → Option Op
  | .source i => readInstr (toCore i)
  | _ => none

/-- Convert through the native version's public source instruction embedding.
All listed local opcodes are in its image. -/
def legacyCodec {I : Type} (toCore : I → Instr) (emit : Op → I)
    (inj : Function.Injective toCore) (agrees : ∀ op, toCore (emit op) = coreInstr op) :
    Codec (AdminInstr I) where
  emit op := .source (emit op)
  read := legacyRead toCore
  read_emit op := by simp [legacyRead, agrees, readInstr_emit]
  emit_read {a op} h := by
    cases a <;> simp [legacyRead] at h
    case source i => exact congrArg AdminInstr.source (inj ((agrees op).trans (readInstr_sound h)))

def v1Instr : Op → Silmaril.Wasm.V1.Instr
  | .value ⟨.int t, x⟩ => .intConst t x
  | .value ⟨.float t, x⟩ => .floatConst t x
  | .get i => .localGet i
  | .set i => .localSet i
  | .tee i => .localTee i

def limeInstr : Op → Silmaril.Wasm.Lime1.Instr
  | .value ⟨.int t, x⟩ => .intConst t x
  | .value ⟨.float t, x⟩ => .floatConst t x
  | .get i => .localGet i
  | .set i => .localSet i
  | .tee i => .localTee i

def v1Codec : Codec Silmaril.Wasm.V1.Execution.Admin :=
  legacyCodec Silmaril.Wasm.V1.Instr.toCore v1Instr Silmaril.Wasm.V1.Instr.toCore_injective (by
    intro op
    cases op with
    | value v => rcases v with ⟨t, x⟩; cases t <;> rfl
    | _ => rfl)

def limeCodec : Codec Silmaril.Wasm.Lime1.Execution.Admin :=
  legacyCodec Silmaril.Wasm.Lime1.Instr.toCore limeInstr Silmaril.Wasm.Lime1.Instr.toCore_injective (by
    intro op
    cases op with
    | value v => rcases v with ⟨t, x⟩; cases t <;> rfl
    | _ => rfl)

def coreCodec : Codec Core.Admin where
  emit op := .plain (coreInstr op)
  read
    | .plain i => readInstr i
    | _ => none
  read_emit := readInstr_emit
  emit_read {a op} h := by
    cases a <;> first | exact congrArg Core.Admin.plain (readInstr_sound h) | cases h

/-- Each renderer takes an explicit store and module instance. The shared frame
contains exactly its initialized numeric locals. -/
def v1Config {H : Type} (s : Silmaril.Wasm.V1.Execution.Store H) (m : Runtime.ModuleInst)
    (a : State) : Silmaril.Wasm.V1.Execution.Config H :=
  ⟨s, ⟨a.locals, m⟩, v1Codec.encode a.code⟩

def limeConfig {H : Type} (s : Silmaril.Wasm.Lime1.Execution.Store H) (m : Runtime.ModuleInst)
    (a : State) : Silmaril.Wasm.Lime1.Execution.Config H :=
  ⟨s, ⟨a.locals, m⟩, limeCodec.encode a.code⟩

def coreLocal (v : Value) : Option Core.Val := some (LegacyDivision.liftValue v)

def coreConfig {H : Type} (s : Core.Store H) (m : Core.ModuleInst) (a : State) : Core.Config H :=
  ⟨s, ⟨a.locals.map coreLocal, m⟩, coreCodec.encode a.code⟩

end Silmaril.Wasm.Institution.Operational.Locals
