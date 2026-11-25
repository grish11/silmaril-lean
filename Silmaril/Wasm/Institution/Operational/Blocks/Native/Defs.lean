module

public import Silmaril.Wasm.Institution.Operational.Blocks.Defs
public import Silmaril.Wasm.Institution.Operational.Locals.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (ModuleInst)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (m : ModuleInst) :
    State → Wasm.V1.Execution.Config H
  | .block result a => ⟨s, ⟨a.locals, m⟩, [.source (.block result (a.code.map Locals.v1Instr))]⟩
  | .label result a => ⟨s, ⟨a.locals, m⟩, [.label result.toList.length [] (Locals.v1Codec.encode a.code)]⟩
  | .done ls vs => ⟨s, ⟨ls, m⟩, Wasm.V1.Execution.values vs⟩

/-- The immediate (unindexed) block types common to all three versions. -/
def limeType : Option NumType → Wasm.Lime1.BlockType
  | none => .empty
  | some t => .value t

def coreType : Option NumType → BlockType
  | none => .empty
  | some t => .value (.num t)

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (m : ModuleInst) :
    State → Wasm.Lime1.Execution.Config H
  | .block result a => ⟨s, ⟨a.locals, m⟩, [.source (.block (limeType result) (a.code.map Locals.limeInstr))]⟩
  | .label result a => ⟨s, ⟨a.locals, m⟩, [.label result.toList.length [] (Locals.limeCodec.encode a.code)]⟩
  | .done ls vs => ⟨s, ⟨ls, m⟩, Wasm.Lime1.Execution.values vs⟩

def coreConfig {H : Type} (s : Core.Store H) (m : Core.ModuleInst) : State → Core.Config H
  | .block result a =>
      ⟨s, ⟨a.locals.map Locals.coreLocal, m⟩, [.plain (.block (coreType result) (a.code.map Locals.coreInstr))]⟩
  | .label result a =>
      ⟨s, ⟨a.locals.map Locals.coreLocal, m⟩, [.label result.toList.length [] (Locals.coreCodec.encode a.code)]⟩
  | .done ls vs => ⟨s, ⟨ls.map Locals.coreLocal, m⟩, Core.vals (vs.map LegacyDivision.liftValue)⟩

end Silmaril.Wasm.Institution.Operational.Blocks
