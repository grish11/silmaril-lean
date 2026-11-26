module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee.Proofs

open Execution.Runtime (Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall (Declaration)
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

theorem get_typed {callee : MemoryTarget} {args stack : List Value} {i : LocalIdx}
    {ops : List Graph.Memory32.Op} (argsTyped : args.map Value.type = callee.fn.declaration.params)
    (typed : callee.fn.WellTyped stack (.ranked (.numeric (.get i)) :: ops)) :
    ∃ v, (callee.fn.declaration.frame args).locals[i.toNat]? = some v ∧
      callee.fn.WellTyped (stack ++ [v]) ops := by
  have locals : (callee.fn.declaration.frame args).locals.map Value.type =
      callee.fn.declaration.params ++ callee.fn.declaration.locals := by
    simp [Declaration.frame, List.map_map, Function.comp_def, Value.zero, argsTyped]
  unfold Graph.Memory32.Function.WellTyped Graph.Memory32.Function.checkCode at typed
  simp only [Graph.Memory32.Function.checkRegion, Graph.Memory32.Function.checkRegionOp,
    Graph.checkOp, Prefix.checkOp] at typed
  rw [← locals, List.getElem?_map] at typed
  cases found : (callee.fn.declaration.frame args).locals[i.toNat]? with
  | none => simp [found] at typed
  | some v =>
    exact ⟨v, rfl, by
      simpa [found, Graph.Memory32.Function.WellTyped, Graph.Memory32.Function.checkCode,
        Prefix.stackTypes, List.reverse_append] using typed⟩

theorem typed_nil {callee : MemoryTarget} {stack : List Value} (typed : callee.fn.WellTyped stack []) :
    resultTyped callee (.values stack) := by
  simpa [Graph.Memory32.Function.WellTyped, Graph.Memory32.Function.checkCode,
    Graph.Memory32.Function.checkRegion, Prefix.stackTypes, resultTyped] using typed

private theorem tail_supported {op : Graph.Memory32.Op} {ops : List Graph.Memory32.Op}
    (checked : (op :: ops).all MemoryTarget.supportedOp = true) :
    ops.all MemoryTarget.supportedOp = true := by
  exact List.all_eq_true.mpr (fun a member => List.all_eq_true.mp checked a (List.mem_cons_of_mem _ member))

theorem ready_step {H : Type} {base : Store H} {mem : Memory32 base} {callee : MemoryTarget}
    {bytes written : ByteArray} {phase next : Phase}
    (checked : callee.Checked mem) (move : Edge callee bytes phase written next)
    (ready : Ready callee phase) : Ready callee next := by
  cases move with
  | enter => exact ⟨ready, checked.supported, checked.body⟩
  | get found =>
    obtain ⟨v, lookup, typed⟩ := get_typed ready.1 ready.2.2
    rw [found] at lookup
    cases lookup
    exact ⟨ready.1, tail_supported ready.2.1, typed⟩
  | load _ =>
    obtain ⟨kept, address, split, typed⟩ := Graph.Memory32.Function.load_typed ready.2.2
    obtain ⟨rfl, _⟩ := List.append_inj' split rfl
    exact ⟨ready.1, tail_supported ready.2.1, typed _⟩
  | store _ =>
    obtain ⟨kept, address, operand, split, typed⟩ := Graph.Memory32.Function.store_typed ready.2.2
    obtain ⟨rfl, _⟩ := List.append_inj' split rfl
    exact ⟨ready.1, tail_supported ready.2.1, typed⟩
  | loadTrap | storeTrap => exact ready.1
  | erase => exact ready
  | labelDone => exact ⟨ready.1, typed_nil ready.2.2⟩
  | labelTrap => exact ⟨ready, trivial⟩
  | frameDone => exact ready.2

theorem live_step {H : Type} {base : Store H} {mem : Memory32 base} {callee : MemoryTarget}
    {bytes written : ByteArray} {phase next : Phase}
    (move : Edge callee bytes phase written next) (live : mem.Live bytes) : mem.Live written := by
  cases move with
  | store write =>
    have same : _ = bytes.size := MemoryWrite.closed_at write
    exact same.trans live
  | _ => exact live

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee.Proofs
