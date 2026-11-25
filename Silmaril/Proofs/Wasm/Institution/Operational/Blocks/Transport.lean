module

public import Silmaril.Wasm.Institution.Operational.Blocks.Native.Defs
public import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Proofs

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (ModuleInst)

private theorem v1Instr_toLime (op : Locals.Op) :
    (Locals.v1Instr op).toLime = Locals.limeInstr op := by
  cases op with
  | value v => rcases v with ⟨t, bits⟩; cases t <;> rfl
  | _ => rfl

private theorem limeInstr_toCore (op : Locals.Op) :
    (Locals.limeInstr op).toCore = Locals.coreInstr op := by
  cases op with
  | value v => rcases v with ⟨t, bits⟩; cases t <;> rfl
  | _ => rfl

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (m : ModuleInst) (a : State) :
    (v1Config s m a).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) m a := by
  cases a with
  | block result body =>
    cases result <;> simp [v1Config, limeConfig, Wasm.V1.Execution.Config.toLime,
      Runtime.AdminInstr.map, Wasm.V1.Instr.toLime, Wasm.V1.Expr.toLime_eq_map, List.map_map, v1Instr_toLime, limeType,
      Wasm.V1.BlockType.toLime]
  | label result body =>
    have code := congrArg (fun c : Wasm.Lime1.Execution.Config H => c.code) (Locals.v1_to_lime s m body)
    change Wasm.V1.Execution.codeToLime (Locals.v1Codec.encode body.code) = _ at code
    change (⟨s.mapCode Wasm.V1.Func.toLime, ⟨body.locals, m⟩,
      [.label result.toList.length [] (Wasm.V1.Execution.codeToLime (Locals.v1Codec.encode body.code))]⟩ :
      Wasm.Lime1.Execution.Config H) = _
    rw [code]
    rfl
  | done ls vs =>
    change (⟨s.mapCode Wasm.V1.Func.toLime, ⟨ls, m⟩,
      Wasm.V1.Execution.codeToLime (Wasm.V1.Execution.values vs)⟩ : Wasm.Lime1.Execution.Config H) = _
    rw [Wasm.V1.Execution.map_values]
    rfl

theorem lime_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H) (m : ModuleInst) (a : State) :
    (limeConfig s m a).toCore = coreConfig s.toCore m.toCore a := by
  cases a with
  | block result body =>
    change (⟨s.toCore, ⟨body.locals.map Locals.coreLocal, m.toCore⟩,
      [.plain ((Wasm.Lime1.Instr.block (limeType result) (body.code.map Locals.limeInstr)).toCore)]⟩ :
      Core.Config H) = _
    have code : (body.code.map Locals.limeInstr).map Wasm.Lime1.Instr.toCore = body.code.map Locals.coreInstr := by
      simp [List.map_map, limeInstr_toCore]
    cases result <;>
      simp [Wasm.Lime1.Instr.toCore, Wasm.Lime1.Expr.toCore_eq_map, coreConfig, limeType, coreType, code,
        Wasm.Lime1.BlockType.toCore]
  | label result body =>
    have code := congrArg Core.Config.code (Locals.lime_to_core s m body)
    change Wasm.Lime1.Execution.Admin.listToCore s (Locals.limeCodec.encode body.code) =
      Locals.coreCodec.encode body.code at code
    change (⟨s.toCore, ⟨body.locals.map Locals.coreLocal, m.toCore⟩,
      [.label result.toList.length []
        (Wasm.Lime1.Execution.Admin.listToCore s (Locals.limeCodec.encode body.code))]⟩ : Core.Config H) = _
    rw [code]
    rfl
  | done ls vs =>
    change (⟨s.toCore, ⟨ls.map Locals.coreLocal, m.toCore⟩,
      Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.values vs)⟩ : Core.Config H) = _
    have values : Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.values vs) =
        Core.vals (vs.map LegacyDivision.liftValue) := by
      induction vs with
      | nil => rfl
      | cons v vs ih =>
        change Wasm.Lime1.Execution.Admin.toCore s (Wasm.Lime1.Execution.value v) ++
          Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.values vs) = _
        rw [ih]
        rcases v with ⟨t, bits⟩
        cases t <;> rfl
    rw [values]
    rfl

end Silmaril.Wasm.Institution.Operational.Blocks.Proofs
