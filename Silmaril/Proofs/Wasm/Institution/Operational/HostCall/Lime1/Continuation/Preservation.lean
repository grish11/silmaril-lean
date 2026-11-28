module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Wasm
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs

open Execution.Runtime (Frame ModuleInst Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall.Ranked

variable {H : Type} {base : Store H} {mem : Memory32 base} {host : HostSemantics H}
  {active : Frame} {targets : List (List NumType)} {results types : List NumType} {ops : List (Op H)}
  {i : LocalIdx} {index : FuncIdx} {site : Site H}

theorem checked_nil (h : Checked base active.module (active.locals.map Value.type) targets results types ([] : List (Op H))) :
    types = results := by cases h; rfl

theorem checked_get (h : Checked base active.module (active.locals.map Value.type) targets results types (.get i :: ops)) :
    ∃ type, (active.locals.map Value.type)[i.toNat]? = some type ∧
      Checked base active.module (active.locals.map Value.type) targets results (types ++ [type]) ops := by
  cases h with
  | get found tail => exact ⟨_, found, tail⟩

theorem checked_drop (h : Checked base active.module (active.locals.map Value.type) targets results types (.drop :: ops)) :
    ∃ saved type, types = saved ++ [type] ∧
      Checked base active.module (active.locals.map Value.type) targets results saved ops := by
  cases h with
  | drop tail => exact ⟨_, _, rfl, tail⟩

theorem checked_call
    (h : Checked base active.module (active.locals.map Value.type) targets results types (.call index site :: ops)) :
    ∃ saved, types = saved ++ site.type.params ∧ active.module.funcs[index.toNat]? = some site.address ∧
      site.Allocated base ∧ Checked base active.module (active.locals.map Value.type) targets results
        (saved ++ site.type.results) ops := by
  cases h with
  | call resolved allocated tail => exact ⟨_, rfl, resolved, allocated, tail⟩

theorem checked_indirect {indirect : IndirectSite}
    (h : Checked base active.module (active.locals.map Value.type) targets results types
      (.callIndirect indirect :: ops)) :
    ∃ saved, types = (saved ++ indirect.signature.params) ++ [.int .i32] ∧
      indirect.Linked base active.module ∧
      Checked base active.module (active.locals.map Value.type) targets results
        (saved ++ indirect.signature.results) ops := by
  cases h with
  | callIndirect linked tail => exact ⟨_, rfl, linked, tail⟩

theorem checked_br {depth : LabelIdx}
    (h : Checked base active.module (active.locals.map Value.type) targets results types (.br depth :: ops)) :
    ∃ scratch payload, types = scratch ++ payload ∧ targets[depth.toNat]? = some payload := by
  cases h with
  | br target => exact ⟨_, _, rfl, target⟩

theorem checked_brIf {depth : LabelIdx}
    (h : Checked base active.module (active.locals.map Value.type) targets results types (.brIf depth :: ops)) :
    ∃ scratch payload, types = (scratch ++ payload) ++ [.int .i32] ∧ targets[depth.toNat]? = some payload ∧
      Checked base active.module (active.locals.map Value.type) targets results (scratch ++ payload) ops := by
  cases h with
  | brIf target tail => exact ⟨_, _, rfl, target, tail⟩

theorem checked_brTable {depths : List LabelIdx} {fallback : LabelIdx}
    (h : Checked base active.module (active.locals.map Value.type) targets results types
      (.brTable depths fallback :: ops)) :
    ∃ scratch payload, types = (scratch ++ payload) ++ [.int .i32] ∧
      (∀ depth ∈ depths, targets[depth.toNat]? = some payload) ∧
      targets[fallback.toNat]? = some payload := by
  cases h with
  | brTable listed defaultTarget => exact ⟨_, _, rfl, listed, defaultTarget⟩

theorem checked_loop {type : IfType} {body : List (Op H)}
    (h : Checked base active.module (active.locals.map Value.type) targets results types (.loop type body :: ops)) :
    ∃ saved, types = saved ++ type.signature.params ∧ type.Resolved active.module ∧
      Checked base active.module (active.locals.map Value.type) (type.signature.params :: targets)
        type.signature.results type.signature.params body ∧
      Checked base active.module (active.locals.map Value.type) targets results (saved ++ type.signature.results) ops := by
  cases h with
  | loop resolved bodyChecked tail => exact ⟨_, rfl, resolved, bodyChecked, tail⟩

theorem checked_if {type : IfType} {left right : List (Op H)}
    (h : Checked base active.module (active.locals.map Value.type) targets results types (.if_ type left right :: ops)) :
    ∃ saved, types = (saved ++ type.signature.params) ++ [.int .i32] ∧ type.Resolved active.module ∧
      Checked base active.module (active.locals.map Value.type) (type.signature.results :: targets) type.signature.results type.signature.params left ∧
      Checked base active.module (active.locals.map Value.type) (type.signature.results :: targets) type.signature.results type.signature.params right ∧
      Checked base active.module (active.locals.map Value.type) targets results (saved ++ type.signature.results) ops := by
  cases h with
  | if_ resolved left right tail => exact ⟨_, rfl, resolved, left, right, tail⟩

private theorem contract_tail {op : Op H} (contract : Contract mem host (op :: ops))
    (continues : match op with | .br _ | .brTable .. => False | _ => True) : Contract mem host ops := by
  cases contract <;> first | assumption | exact False.elim continues

private theorem contract_call (contract : Contract mem host (.call index site :: ops)) : site.Contract mem host := by
  cases contract with
  | call contract _ => exact contract

theorem live_step {a b : State H} (edge : Edge mem host active results a b) (live : mem.Live a.bytes) : mem.Live b.bytes := by
  cases edge <;> try assumption
  case memory move => exact MemoryCallee.live_step move live

theorem ready_step {a b : State H} (edge : Edge mem host active results a b)
    (ready : Ready mem host active results a.phase a.labels) : Ready mem host active results b.phase b.labels := by
  cases edge with
  | get found =>
    obtain ⟨type, lookup, tail⟩ := checked_get ready.2.1
    rw [List.getElem?_map, found] at lookup
    cases lookup
    exact ⟨ready.1, by simpa only [List.map_append, List.map_cons, List.map_nil] using tail, contract_tail ready.2.2 trivial⟩
  | drop =>
    obtain ⟨_, _, split, tail⟩ := checked_drop ready.2.1
    simp only [List.map_append, List.map_cons, List.map_nil] at split
    have same := (List.append_inj' split rfl).1
    exact ⟨ready.1, same ▸ tail, contract_tail ready.2.2 trivial⟩
  | brIf =>
    obtain ⟨scratch, payload, stackEq, target, tail⟩ := checked_brIf ready.2.1
    simp only [List.map_append, List.map_cons, List.map_nil, Value.int] at stackEq
    have operands := List.append_cancel_right stackEq
    split
    · exact ⟨ready.1, operands.symm ▸ tail, contract_tail ready.2.2 trivial⟩
    · exact ⟨ready.1, operands.symm ▸ Checked.br target, .br⟩
  | @brTable bytes stack selector depths fallback ops labels =>
    obtain ⟨scratch, payload, stackEq, listed, defaultTarget⟩ := checked_brTable ready.2.1
    simp only [List.map_append, List.map_cons, List.map_nil, Value.int] at stackEq
    have operands := List.append_cancel_right stackEq
    have selected : (targetTypes results labels)[(depths[selector.toNat]?.getD fallback).toNat]? = some payload := by
      cases found : depths[selector.toNat]? with
      | none => exact defaultTarget
      | some depth => exact listed depth (List.mem_of_getElem? found)
    exact ⟨ready.1, operands.symm ▸ Checked.br selected, .br⟩
  | @branchLower bytes stack depth ops label labels positive =>
    obtain ⟨scratch, payload, typed, target⟩ := checked_br ready.2.1
    cases ready.1 with
    | cons _ _ _ outer =>
      cases depthEq : depth.toNat with
      | zero => omega
      | succ depth' =>
        have lowered : (lowerLabel depth).toNat = depth' := by
          change depth.toNat - 1 = depth'
          omega
        have nextTarget : (targetTypes results labels)[(lowerLabel depth).toNat]? = some payload := by
          simpa only [targetTypes, lowered, depthEq, List.getElem?_cons_succ] using target
        refine ⟨outer, ?_, .br⟩
        have next : Checked base active.module (active.locals.map Value.type) (targetTypes results labels)
            (labelResults results labels) ((label.saved.map Value.type ++ scratch) ++ payload)
            (.br (lowerLabel depth) :: label.tail) := .br nextTarget
        simpa only [List.map_append, typed, List.append_assoc] using next
  | branchDeliver _ _ typed =>
    cases ready.1 with
    | cons tail contract _ outer =>
      exact ⟨outer, by simpa only [List.map_append, typed] using tail, contract⟩
  | branchRestart _ loopBody typed =>
    cases ready.1 with
    | cons tail tailContract restart outer =>
      simp only [Label.RestartReady, loopBody] at restart
      obtain ⟨resolved, bodyChecked, bodyContract⟩ := restart
      refine ⟨outer, ?_, .loop bodyContract tailContract⟩
      simpa only [List.map_append, typed] using Checked.loop resolved bodyChecked tail
  | functionBranch _ typed => exact ⟨.nil, rfl, typed⟩
  | @if_ bytes saved args guard type left right ops labels typed =>
    obtain ⟨savedTypes, stackEq, resolved, leftChecked, rightChecked, tail⟩ := checked_if ready.2.1
    simp only [List.map_append, List.map_cons, List.map_nil, Value.int, typed] at stackEq
    have same := List.append_cancel_right (List.append_cancel_right stackEq)
    obtain ⟨labelReady, _, contract⟩ := ready
    cases contract with
    | if_ leftContract rightContract tailContract =>
      have tailChecked : Checked base active.module (active.locals.map Value.type) (targetTypes results labels)
          (labelResults results labels)
          (saved.map Value.type ++ type.signature.results) ops := same.symm ▸ tail
      have selected : Checked base active.module (active.locals.map Value.type)
          (type.signature.results :: targetTypes results labels) type.signature.results type.signature.params
          (select guard left right) ∧ Contract mem host (select guard left right) := by
        by_cases zero : guard = 0
        · rw [show select guard left right = right from ite_eq_left zero]
          exact ⟨rightChecked, rightContract⟩
        · rw [show select guard left right = left from ite_eq_right zero]
          exact ⟨leftChecked, leftContract⟩
      exact ⟨labelReady, rfl, resolved, typed, typed.symm ▸ selected.1, selected.2, tailChecked, tailContract⟩
  | @block bytes label args arm labels exits =>
    obtain ⟨labelsReady, _, _, _, armChecked, armContract, tailChecked, tailContract⟩ := ready
    have restart : label.RestartReady mem host active (targetTypes results labels) := by
      simp [Label.RestartReady, exits]
    refine ⟨.cons tailChecked tailContract restart labelsReady, ?_, armContract⟩
    simpa [targetTypes, Label.branchTypes, exits, labelResults] using armChecked
  | @loop bytes saved args type body ops labels typed =>
    obtain ⟨_, stackEq, resolved, bodyChecked, tail⟩ := checked_loop ready.2.1
    simp only [List.map_append, typed] at stackEq
    have same := List.append_cancel_right stackEq
    cases ready.2.2 with
    | loop bodyContract tailContract =>
      have tailChecked : Checked base active.module (active.locals.map Value.type)
          (targetTypes results labels) (labelResults results labels) (saved.map Value.type ++ type.signature.results) ops :=
        same.symm ▸ tail
      exact ⟨.cons tailChecked tailContract ⟨resolved, bodyChecked, bodyContract⟩ ready.1,
        typed.symm ▸ bodyChecked, bodyContract⟩
  | resolve typed =>
    obtain ⟨_, split, _, allocated, tail⟩ := checked_call ready.2.1
    simp only [List.map_append] at split
    rw [show _ = _ from typed] at split
    have same := List.append_cancel_right split
    exact ⟨ready.1, allocated, typed, contract_call ready.2.2, same ▸ tail, contract_tail ready.2.2 trivial⟩
  | @callIndirect bytes saved args selector indirect target ops labels typed found =>
    cases found with
    | bounds | null | mismatch => exact ⟨ready.1, trivial⟩
    | @host address code entry allocated =>
      obtain ⟨_, split, _, tail⟩ := checked_indirect ready.2.1
      simp only [List.map_append, List.map_cons, List.map_nil, Value.int, typed] at split
      have same := List.append_cancel_right (List.append_cancel_right split)
      cases ready.2.2 with
      | callIndirect contract tailContract =>
        exact ⟨ready.1, allocated, typed, contract.hosts address code (List.mem_of_getElem? entry) allocated,
          same ▸ tail, tailContract⟩
    | @wasm callee _ present _ declared =>
      obtain ⟨_, split, linked, tail⟩ := checked_indirect ready.2.1
      simp only [List.map_append, List.map_cons, List.map_nil, Value.int, typed] at split
      have same := List.append_cancel_right (List.append_cancel_right split)
      have arguments : args.map Value.type = callee.fn.declaration.params :=
        typed.trans (congrArg V1.FuncType.params declared).symm
      exact ⟨ready.1, linked, present, declared, by simp, by simp, .invoke arguments,
        same ▸ tail, contract_tail ready.2.2 trivial⟩
    | @memory callee _ found allocated declared =>
      obtain ⟨_, split, _, tail⟩ := checked_indirect ready.2.1
      simp only [List.map_append, List.map_cons, List.map_nil, Value.int, typed] at split
      have same := List.append_cancel_right (List.append_cancel_right split)
      have arguments : args.map Value.type = callee.fn.declaration.params :=
        typed.trans (congrArg V1.FuncType.params declared).symm
      have resultTypes : callee.fn.declaration.results = indirect.signature.results :=
        congrArg V1.FuncType.results declared
      cases ready.2.2 with
      | callIndirect contract tailContract =>
        exact ⟨ready.1, allocated, found, contract.memory.forFiniteRun, by simp, ⟨arguments, rfl, rfl⟩,
          by simpa only [resultTypes, same] using tail, tailContract⟩
  | @wasm bytes saved site callee phase next ops labels move =>
    obtain ⟨labelsReady, linked, found, declared, _, _, admitted, tail, contract⟩ := ready
    have admittedNext := site.graph.frame_admitted_step linked.graphChecked found admitted move
    have notCall := wasm_next_not_call found move
    cases next <;> try exact ⟨labelsReady, linked, found, declared, notCall, by simp, admittedNext, tail, contract⟩
    case done outcome =>
      cases outcome with
      | trap => exact ⟨labelsReady, trivial⟩
      | values vs =>
        have typed : vs.map Value.type = callee.fn.declaration.results := by
          cases admittedNext with
          | done valueTypes => exact valueTypes
        have delivered := typed.trans (congrArg V1.FuncType.results declared)
        exact ⟨labelsReady, by simpa only [List.map_append, delivered] using tail, contract⟩
  | @memory bytes written saved site callee phase next ops labels move =>
    obtain ⟨labelsReady, allocated, registered, linked, _, admitted, tail, contract⟩ := ready
    have admittedNext := MemoryCallee.ready_step linked registered move admitted
    cases next <;> try exact ⟨labelsReady, allocated, registered, linked, by simp, admittedNext, tail, contract⟩
    case done out =>
      cases out with
      | trap => exact ⟨labelsReady, trivial⟩
      | values vs =>
        have typed : vs.map Value.type = callee.fn.declaration.results := admittedNext
        exact ⟨labelsReady, by simpa only [List.map_append, typed] using tail, contract⟩
  | returned _ typed _ =>
    refine ⟨ready.1, ?_, ready.2.2.2.2.2⟩
    simpa only [List.map_append, show _ = _ from typed] using ready.2.2.2.2.1
  | trapped | erase => exact ⟨ready.1, trivial⟩
  | armResult =>
    have typed := checked_nil ready.2.1
    cases ready.1 with
    | cons tail contract _ outer =>
      exact ⟨outer, by simpa only [List.map_append, typed, labelResults] using tail, contract⟩
  | armTrap =>
    cases ready.1 with
    | cons _ _ _ outer => exact ⟨outer, trivial⟩
  | labelTrap => exact ⟨.nil, rfl, trivial⟩
  | diverged | frameDone => exact ready
  | labelResult => exact ⟨.nil, rfl, checked_nil ready.2.1⟩

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs
