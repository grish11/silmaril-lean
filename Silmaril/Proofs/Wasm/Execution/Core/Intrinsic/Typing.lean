module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Defs

public section

namespace Silmaril.Proofs.Wasm.Execution.Core.Intrinsic

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Execution.Core.Intrinsic

variable {H : Type} {context : Context} {kind : IntType}
  {locals input middle output : List IntType}

private theorem stackTypes_ok (context : Context) (types : List IntType) :
    ResultOk context.toTypeCtx (stackTypes types) := by
  intro type member
  obtain ⟨kind, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp member)
  exact .num (.int kind)

theorem slot_type (ref : Slot locals kind) :
    (localTypes locals)[ref.toNat]? = some ⟨.set, .num (.int kind)⟩ := by
  induction ref with
  | here => rfl
  | there ref ih => simpa [Slot.toNat, localTypes] using ih

theorem slot_value (ref : Slot locals kind) (values : Values locals) :
    (values.erase.map some)[ref.toNat]? = some (some (.num ⟨.int kind, ref.get values⟩)) := by
  induction ref with
  | here => cases values; rfl
  | there ref ih =>
    cases values with
    | cons bits tail => simpa [Slot.toNat, Slot.get, Values.erase] using ih tail

private theorem op_ok (op : Op locals input output) (h : context.locals = localTypes locals) :
    InstrsOk context [op.erase] (.plain (stackTypes input) (stackTypes output)) := by
  cases op with
  | nop =>
    simpa [Op.erase] using
      InstrsOk.frame (.instr (.parametric .nop)) (stackTypes_ok context input)
  | @drop kind _ =>
    simpa [Op.erase, stackTypes] using
      InstrsOk.frame (.instr (.parametric (.drop (.num (.int kind))))) (stackTypes_ok context output)
  | @localGet kind _ ref bound =>
    have lookup : context.locals[(ref.index bound).toNat]? = some ⟨.set, .num (.int kind)⟩ := by
      rw [h]; exact slot_type ref
    simpa [Op.erase, stackTypes] using
      InstrsOk.frame (.instr (.variable (.localGet lookup))) (stackTypes_ok context input)
  | @intBin kind _ op =>
    simp only [Op.erase, stackTypes, List.map_cons, List.reverse_cons, List.append_assoc]
    exact InstrsOk.frame (.instr (.numeric (.intBinOp kind op))) (stackTypes_ok context _)
  | unreachable =>
    exact .instr (.parametric (.unreachable ⟨stackTypes_ok context _, stackTypes_ok context _,
      by simp⟩))

theorem code_ok (code : Code locals input output) (h : context.locals = localTypes locals) :
    InstrsOk context code.erase (.plain (stackTypes input) (stackTypes output)) := by
  induction code with
  | @done stack =>
    simpa [Code.erase] using InstrsOk.frame .nil (stackTypes_ok context stack)
  | seq op tail ih =>
    exact InstrsOk.seq (op_ok op h) (by simp) ih

theorem append_erase (left : Code locals input middle) (right : Code locals middle output) :
    (left.append right).erase = left.erase ++ right.erase := by
  induction left with
  | done => rfl
  | seq op tail ih => simp [Code.append, Code.erase, ih]

private theorem locals_ok (store : Store H) (values : Values locals) :
    List.Forall₂ (LocalValOk store) (values.erase.map some) (localTypes locals) := by
  induction values with
  | nil => exact .nil
  | cons bits tail ih => exact .cons (.set (.num _)) ih

private theorem module_locals {store : Store H} {inst : ModuleInst}
    (h : ModuleInstOk store inst context) : context.locals = [] := by
  cases h; rfl

theorem frame_ok {world : World H context} (frame : LocalFrame world locals) :
    FrameOk world.store frame.erase {context with locals := localTypes locals} :=
  ⟨context, localTypes locals, world.moduleOk, locals_ok _ frame.values,
    by simp [module_locals world.moduleOk]⟩

private theorem stack_ok (store : Store H) (context : Context) (values : Values input) :
    AdminsOk store context (vals values.erase.reverse) (.plain [] (stackTypes input)) := by
  induction values with
  | nil => exact .nil
  | @cons kind tailTypes bits tail ih =>
    have one : AdminsOk store context [.plain (.intConst kind bits)] (.plain [] [.num (.int kind)]) :=
      .single (.plain (.numeric (.intConst kind bits)))
    have shifted : AdminsOk store context [.plain (.intConst kind bits)]
        (.plain (stackTypes tailTypes) (stackTypes tailTypes ++ [.num (.int kind)])) := by
      simpa using AdminsOk.frame one (stackTypes_ok context tailTypes)
    have combined := AdminsOk.seq ih (by simp) shifted
    simpa [stackTypes, Values.erase, vals, Val.toAdmin] using combined

theorem state_ok {world : World H context} (state : State world locals output) :
    ConfigOk state.erase (stackTypes output) := by
  let ctx := {context with locals := localTypes locals}
  refine ⟨ctx, ⟨world.storeOk, frame_ok state.frame⟩, ?_⟩
  cases state with
  | mk frame control =>
    cases control with
    | run values code =>
      exact .seq (stack_ok world.store ctx values) (by simp)
        (.of_instrsOk (code_ok code rfl))
    | trapping values code =>
      simp only [State.erase, Control.erase, List.append_assoc, List.singleton_append]
      refine .seq (stack_ok world.store ctx values) (by simp) ?_
      exact AdminsOk.cons (xs₁ := []) (.trap ⟨stackTypes_ok ctx _, stackTypes_ok ctx _, by simp⟩) (by simp)
        (.of_instrsOk (code_ok code rfl))

end Silmaril.Proofs.Wasm.Execution.Core.Intrinsic
