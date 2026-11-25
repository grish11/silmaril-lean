module

public import Silmaril.Wasm.Institution.Operational.Locals.Native.Defs
public import Silmaril.Wasm.Versions.Lime1.Runtime.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Locals.Proofs

open Silmaril.Wasm.Execution.Runtime (AdminInstr)
open Silmaril.Wasm.V1.Execution (codeToLime)

theorem run_iff {C : Type} (emit : State → C) (native : C → C → Prop)
    (sound : ∀ {a b}, Edge a b → native (emit a) (emit b))
    (readback : ∀ {a b}, native (emit a) b → ∃ out, Edge a out ∧ b = emit out)
    {types result : List NumType} {a : State} {b : C} (guard : Admitted types result a) :
    Relation.ReflTransGen native (emit a) b ↔
      ∃ out, Runs a out ∧ Admitted types result out ∧ b = emit out := by
  constructor
  · intro run
    induction run with
    | refl => exact ⟨a, .refl, guard, rfl⟩
    | tail _ step ih =>
      obtain ⟨middle, path, ready, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := readback step
      exact ⟨out, path.tail edge, closed ready edge, rfl⟩
  · rintro ⟨out, path, _, rfl⟩
    exact Relation.ReflTransGen.lift emit (fun _ _ h => sound h) _ _ path

private theorem emit_toLime (op : Op) :
    AdminInstr.map Wasm.V1.Instr.toLime (v1Codec.emit op) = limeCodec.emit op := by
  cases op with
  | value v => rcases v with ⟨t, bits⟩; cases t <;> rfl
  | _ => rfl

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H)
    (m : Wasm.Execution.Runtime.ModuleInst) (a : State) :
    (v1Config s m a).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) m a := by
  have code : codeToLime (v1Codec.encode a.code) = limeCodec.encode a.code := by
    simp [Codec.encode, AdminInstr.mapList_eq_map, List.map_map, emit_toLime]
  simp only [v1Config, limeConfig, Wasm.V1.Execution.Config.toLime, code]

theorem emit_core {I : Type} (toCore : I → Instr) (emit : Op → I)
    (inj : Function.Injective toCore) (agrees : ∀ op, toCore (emit op) = coreInstr op)
    (ops : List Op) :
    LegacyDivision.emitCode toCore ((legacyCodec toCore emit inj agrees).encode ops) =
      coreCodec.encode ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    change Wasm.Execution.Core.Admin.plain (toCore (emit op)) :: _ =
      Wasm.Execution.Core.Admin.plain (coreInstr op) :: _
    exact congrArg₂ List.cons (congrArg _ (agrees op)) ih

private theorem lime_admin_toCore {H : Type} (s : Wasm.Lime1.Execution.Store H)
    (op : Op) : Wasm.Lime1.Execution.Admin.toCore s (limeCodec.emit op) = [coreCodec.emit op] := by
  cases op with
  | value v => rcases v with ⟨t, bits⟩; cases t <;> rfl
  | _ => rfl

private theorem lime_code_toCore {H : Type} (s : Wasm.Lime1.Execution.Store H)
    (ops : List Op) :
    Wasm.Lime1.Execution.Admin.listToCore s (limeCodec.encode ops) = coreCodec.encode ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    change Wasm.Lime1.Execution.Admin.toCore s (limeCodec.emit op) ++
      Wasm.Lime1.Execution.Admin.listToCore s (limeCodec.encode ops) =
      coreCodec.emit op :: coreCodec.encode ops
    rw [lime_admin_toCore, ih]
    rfl

theorem lime_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H)
    (m : Wasm.Execution.Runtime.ModuleInst) (a : State) :
    (limeConfig s m a).toCore = coreConfig s.toCore m.toCore a := by
  change (⟨s.toCore, ⟨a.locals.map coreLocal, m.toCore⟩,
    Wasm.Lime1.Execution.Admin.listToCore s (limeCodec.encode a.code)⟩ : Wasm.Execution.Core.Config H) = _
  rw [lime_code_toCore]
  rfl

end Silmaril.Wasm.Institution.Operational.Locals.Proofs
