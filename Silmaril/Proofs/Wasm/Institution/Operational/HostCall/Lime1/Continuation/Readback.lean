module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Preservation
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Context
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Wasm
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Thms
import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs

open Execution.Runtime (EvalCtx Frame Result Value)
open Wasm.Lime1.Execution
open CallContinuation
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Ranked

set_option backward.isDefEq.respectTransparency false

variable {H : Type} {base : Store H} {mem : Memory32 base} {host : HostSemantics H}
  {outer active : Frame} {labels : List (Label H)} {results : List NumType}
  {bytes : ByteArray} {dst : Config H}


private theorem withoutCallout {src : Config H} (absent : decompose? src = none) :
    Step host src dst ↔ Internal src dst := by
  apply Step.internal_iff_of_not_callout
  intro call located
  have found := exists_callout_iff.mp ⟨call, located⟩
  simp [absent] at found

private theorem underLabel {body : List Admin}
    (stays : ∀ out, ¬ PureStep active.module.types [.label (labelBranchTypes results labels).length (labelContinuation labels) body] out)
    (move : Internal ⟨mem.store bytes, outer, framed active [.label (labelBranchTypes results labels).length (labelContinuation labels) body] (scopeFor results labels)⟩ dst) :
    ∃ mid, Internal ⟨mem.store bytes, active, body⟩ mid ∧ dst =
      ⟨mid.store, outer, framed mid.frame [.label (labelBranchTypes results labels).length (labelContinuation labels) mid.code] (scopeFor results labels)⟩ := by
  rcases body_cases move with inside | ⟨out, exiting, _⟩
  · exact inside
  · exact (stays out exiting).elim

private theorem closeLabel {r : Result}
    (move : Internal ⟨mem.store bytes, outer, framed active [.label (labelBranchTypes results labels).length (labelContinuation labels) (result r)] (scopeFor results labels)⟩ dst) :
    dst = ⟨mem.store bytes, outer, framed active (result r) (scopeFor results labels)⟩ := by
  cases r with
  | values vs =>
    rcases body_cases move with ⟨_, inside, _⟩ | ⟨_, pop, rfl⟩
    · exact (Nested.lime_result_stuck (r := .values vs) inside).elim
    · rw [Nested.lime_label_result (r := .values vs) pop]
      rfl
  | trap =>
    rcases body_cases move with ⟨_, inside, _⟩ | ⟨_, pop, rfl⟩
    · exact (Nested.lime_result_stuck (r := .trap) inside).elim
    · rw [Nested.lime_label_result (r := .trap) pop]
      rfl

private theorem located {site : Site H} {args saved : List Value} {ops : List (Op H)}
    (allocated : site.Allocated base) (typed : site.Arguments args) :
    CalloutAt (render mem outer active results ⟨bytes, .invoke saved site args ops, labels⟩)
      (site.callout (invokeContext (scopeFor results labels) (labelBranchTypes results labels).length (labelContinuation labels) active saved ops) args) :=
  ⟨rfl, allocated, by simpa [Site.callout] using congrArg List.length typed⟩

private theorem invoke_read {saved args : List Value} {site : Site H} {ops : List (Op H)}
    (ready : Ready mem host active results (.invoke saved site args ops) labels) (live : mem.Live bytes)
    (move : Step host (render mem outer active results ⟨bytes, .invoke saved site args ops, labels⟩) dst) :
    ∃ next, Edge mem host active results ⟨bytes, .invoke saved site args ops, labels⟩ next ∧
      dst = render mem outer active results next := by
  obtain ⟨_, allocated, typed, contract, _, _⟩ := ready
  have exactStep := Site.step_iff (dst := dst) (outer := outer)
    (context := invokeContext (scopeFor results labels) (labelBranchTypes results labels).length (labelContinuation labels) active saved ops) allocated contract live typed
  rcases exactStep.mp move with ⟨next, out, nLive, nTyped, answer, rfl⟩ | ⟨diverges, rfl⟩
  · cases out with
    | values vs => exact ⟨⟨next, .source (saved ++ vs) ops, labels⟩, .returned nLive nTyped answer,
        by simp [render, Phase.renderCode, Phase.renderIn, plug_invoke, result, List.append_assoc]⟩
    | trap => exact ⟨⟨next, .trapped saved (code ops), labels⟩, .trapped nLive answer,
        by simp [render, Phase.renderCode, Phase.renderIn, plug_invoke, result]⟩
  · exact ⟨_, .diverged diverges, rfl⟩

private theorem branch_read {stack : List Value} {depth : LabelIdx} {ops : List (Op H)}
    (ready : Ready mem host active results (.branch stack depth ops) labels)
    (move : Internal (render mem outer active results ⟨bytes, .branch stack depth ops, labels⟩) dst) :
    ∃ next, Edge mem host active results ⟨bytes, .branch stack depth ops, labels⟩ next ∧
      dst = render mem outer active results next := by
  obtain ⟨_, _, typed, target⟩ := checked_br ready.2.1
  rcases body_cases move with ⟨_, inside, _⟩ | ⟨out, pop, rfl⟩
  · exact (BranchExit.lime_br_vals_stuck inside).elim
  · rcases BranchExit.lime_label_br_cont_iff.mp (Step.pure (host := host) (mem.store bytes) active pop) with
      ⟨scratch, used, split, arity, zero, native⟩ | ⟨positive, native⟩
    · have first : (targetTypes results labels)[0]? = some (labelBranchTypes results labels) := by
        cases labels <;> rfl
      rw [zero, first] at target
      cases target
      obtain ⟨_, payload, typedSplit, _, payloadTyped⟩ := List.map_eq_append_iff.mp typed
      have size : payload.length = (labelBranchTypes results labels).length := by
        simpa using congrArg List.length payloadTyped
      have same := (List.append_inj' (split.symm.trans typedSplit) (arity.trans size.symm)).2
      subst used
      rw [typedSplit]
      cases native
      cases labels with
      | nil => exact ⟨_, .functionBranch zero payloadTyped, by
          simp [render, Phase.renderCode, Phase.renderIn, scopeFor, framed, labelContinuation, expression, result]⟩
      | cons label labels =>
        cases loopBody : label.restart with
        | none =>
          have typed : payload.map Value.type = label.type.signature.results := by
            simpa [labelBranchTypes, Label.branchTypes, loopBody] using payloadTyped
          exact ⟨_, .branchDeliver zero loopBody typed, by
            simp [render, Phase.renderCode, Phase.renderIn, scopeFor, framed, values_append,
              labelContinuation, Label.continuation, loopBody, expression]⟩
        | some body =>
          have typed : payload.map Value.type = label.type.signature.params := by
            simpa [labelBranchTypes, Label.branchTypes, loopBody] using payloadTyped
          exact ⟨_, .branchRestart zero loopBody typed, by
            simp [render, Phase.renderCode, Phase.renderIn, scopeFor, framed, values_append,
              labelContinuation, Label.continuation, loopBody, code, expr, Op.instr, expression, List.append_assoc]⟩
    · cases labels with
      | nil =>
        have outside : (targetTypes results ([] : List (Label H)))[depth.toNat]? = none :=
          List.getElem?_eq_none (by change 1 ≤ depth.toNat; omega)
        rw [outside] at target
        cases target
      | cons label labels =>
        cases native
        exact ⟨_, .branchLower positive, by
          simp only [render, Phase.renderCode, Phase.renderIn, scopeFor, framed,
            code, expr, Op.instr, expression, List.map_cons, values_append, List.append_assoc, List.singleton_append]⟩

private theorem loop_step {saved args : List Value} {type : IfType} {body ops : List (Op H)}
    (resolved : type.Resolved active.module) (typed : args.map Value.type = type.signature.params) :
    Internal ⟨mem.store bytes, active, values (saved ++ args) ++
      .source (.loop type.blockType (expr body)) :: code ops⟩ dst ↔
      dst = ⟨mem.store bytes, active, values saved ++
        .label type.signature.params.length [.loop type.blockType (expr body)] (values args ++ code body) :: code ops⟩ := by
  have arity : args.length = type.signature.params.length := by
    simpa using congrArg List.length typed
  change Step CallFrame.limeNoHost _ _ ↔ _
  rw [Computed.lime_loop_step_iff]
  constructor
  · rintro ⟨kept, used, signature, split, lookup, size, rfl⟩
    change blockType? active.module.types type.blockType = some type.signature at resolved
    rw [resolved] at lookup
    cases lookup
    obtain ⟨rfl, rfl⟩ := List.append_inj' split (arity.trans size.symm)
    rfl
  · intro same
    exact ⟨saved, args, type.signature, rfl, resolved, arity, same⟩

private theorem i32_suffix {stack : List Value} {types : List NumType}
    (typed : stack.map Value.type = types ++ [.int .i32]) :
    ∃ (operands : List Value) (test : BitVec 32), stack = operands ++ [Value.int .i32 test] ∧ operands.map Value.type = types := by
  obtain ⟨operands, suffix, rfl, operandsTyped, testTyped⟩ := List.map_eq_append_iff.mp typed
  obtain ⟨v, rest, rfl, vt, testEmpty⟩ := List.map_eq_cons_iff.mp testTyped
  obtain rfl := List.map_eq_nil_iff.mp testEmpty
  rcases v with ⟨type, bits⟩
  cases vt
  exact ⟨operands, bits, rfl, operandsTyped⟩

private theorem render_lookup {saved args : List Value} {indirect : IndirectSite}
    {target : Option (IndirectTarget H)} {ops : List (Op H)} :
    render mem outer active results ⟨bytes, .afterLookup saved args indirect target ops, labels⟩ =
      ⟨mem.store bytes, outer, framed active [.label (labelBranchTypes results labels).length
        (labelContinuation labels) (values (saved ++ args) ++ IndirectSite.lookupHead target :: code ops)]
        (scopeFor results labels)⟩ := by
  cases target with
  | none => rfl
  | some target =>
    cases target <;> simp [render, Phase.afterLookup, Phase.renderCode, Phase.renderIn, IndirectSite.lookupHead,
      plug_invoke, Graph.Phase.render, Graph.Phase.renderAt, Graph.limeAdmin, WasmTarget.callTarget, MemoryCallee.render,
      values_append, List.append_assoc]

private theorem render_wasm {saved : List Value} {site : IndirectSite} {callee : WasmTarget}
    {phase : Graph.Phase} {ops : List (Op H)} :
    render mem outer active results ⟨bytes, .afterWasm saved site callee ops phase, labels⟩ =
      ⟨mem.store bytes, outer, framed active [.label (labelBranchTypes results labels).length
        (labelContinuation labels) (values saved ++ phase.render Graph.limeAdmin callee.callTarget ++ code ops)]
        (scopeFor results labels)⟩ := by
  cases phase <;> try rfl
  case done out =>
    cases out <;> simp [render, Phase.afterWasm, Phase.renderCode, Phase.renderIn,
      Graph.Phase.render, Graph.Phase.renderAt, Graph.limeAdmin, Nested.resultCode, values_append, List.append_assoc]

private theorem wasm_read {saved : List Value} {site : IndirectSite} {callee : WasmTarget}
    {phase : Graph.Phase} {ops : List (Op H)}
    (ready : Ready mem host active results (.wasm saved site callee phase ops) labels)
    (move : Step host (render mem outer active results ⟨bytes, .wasm saved site callee phase ops, labels⟩) dst) :
    ∃ next, Edge mem host active results ⟨bytes, .wasm saved site callee phase ops, labels⟩ next ∧
      dst = render mem outer active results next := by
  obtain ⟨_, linked, found, _, notCall, notDone, admitted, _, _⟩ := ready
  have allocated : site.graph.LimeAllocated (mem.store bytes) := linked.graphAllocated
  have absent : decompose? (render mem outer active results ⟨bytes, .wasm saved site callee phase ops, labels⟩) = none :=
    noLabelCallout (wasm_absent allocated found admitted saved (code ops) notCall notDone)
  obtain ⟨mid, inside, rfl⟩ := underLabel (fun _ => wasm_stays callee notCall notDone)
    ((withoutCallout absent).mp move)
  obtain ⟨next, edge, rfl⟩ := (wasm_step_iff linked.graphChecked allocated found admitted notCall notDone).mp inside
  exact ⟨_, .wasm edge, render_wasm.symm⟩

private theorem render_memory {saved : List Value} {callee : MemoryTarget}
    {phase : MemoryCallee.Phase} {ops : List (Op H)} :
    render mem outer active results ⟨bytes, .afterMemory saved callee ops phase, labels⟩ =
      ⟨mem.store bytes, outer, framed active [.label (labelBranchTypes results labels).length
        (labelContinuation labels) (values saved ++ MemoryCallee.render callee phase ++ code ops)]
        (scopeFor results labels)⟩ := by
  cases phase <;> try rfl
  case done out =>
    cases out <;> simp [render, Phase.afterMemory, Phase.renderCode, Phase.renderIn,
      MemoryCallee.render, result, values_append, List.append_assoc]

private theorem memory_read {saved : List Value} {callee : MemoryTarget}
    {phase : MemoryCallee.Phase} {ops : List (Op H)}
    (ready : Ready mem host active results (.memory saved callee phase ops) labels) (live : mem.Live bytes)
    (move : Step host (render mem outer active results ⟨bytes, .memory saved callee phase ops, labels⟩) dst) :
    ∃ next, Edge mem host active results ⟨bytes, .memory saved callee phase ops, labels⟩ next ∧
      dst = render mem outer active results next := by
  obtain ⟨_, allocated, checked, notDone, admitted, _, _⟩ := ready
  have liveAllocation : callee.Allocated (mem.store bytes) := allocated
  have absent : decompose? (render mem outer active results ⟨bytes, .memory saved callee phase ops, labels⟩) = none :=
    noLabelCallout (MemoryCallee.absent (mem.store bytes) liveAllocation notDone)
  obtain ⟨mid, inside, rfl⟩ := underLabel (fun _ => MemoryCallee.stays notDone)
    ((withoutCallout absent).mp move)
  obtain ⟨written, next, edge, rfl⟩ := (MemoryCallee.step_iff checked allocated admitted live notDone).mp inside
  exact ⟨_, .memory edge, render_memory.symm⟩

private theorem source_read {stack : List Value} {ops : List (Op H)}
    (ready : Ready mem host active results (.source stack ops) labels)
    (move : Internal (render mem outer active results ⟨bytes, .source stack ops, labels⟩) dst) :
    ∃ next, Edge mem host active results ⟨bytes, .source stack ops, labels⟩ next ∧
      dst = render mem outer active results next := by
  cases ops with
  | nil =>
    have step : Internal ⟨mem.store bytes, outer, framed active [.label (labelBranchTypes results labels).length (labelContinuation labels) (result (.values stack))] (scopeFor results labels)⟩ dst := by
      simpa [render, Phase.renderCode, Phase.renderIn, code, expr, expression, result] using move
    have exit := closeLabel (r := .values stack) step
    cases labels with
    | nil => exact ⟨⟨bytes, .frameResult (.values stack), []⟩, .labelResult, exit⟩
    | cons label rest =>
      exact ⟨⟨bytes, .source (label.saved ++ stack) label.tail, rest⟩, .armResult,
        by simpa [render, Phase.renderCode, Phase.renderIn, framed, scopeFor, result, List.append_assoc] using exit⟩
  | cons op ops =>
    by_cases branch : ∃ depth, op = .br depth
    · obtain ⟨depth, rfl⟩ := branch
      exact branch_read ready move
    have notBranch (depth : LabelIdx) : (.source op.instr : Admin) ≠ .source (.br depth) := by
      intro eq
      apply branch
      cases op <;> simp_all [Op.instr]
    have stay (out : List Admin) : ¬ PureStep active.module.types
        [.label (labelBranchTypes results labels).length (labelContinuation labels) (values stack ++ .source op.instr :: code ops)] out :=
      Computed.lime_label_stays (by cases op <;> rfl) notBranch
        (by cases op <;> simp [Op.instr]) (by simp)
    obtain ⟨mid, inside, rfl⟩ := underLabel stay move
    cases op with
    | get i =>
      obtain ⟨type, lookup, _⟩ := checked_get ready.2.1
      rw [List.getElem?_map] at lookup
      obtain ⟨v, found, _⟩ := Option.map_eq_some_iff.mp lookup
      obtain rfl := (Computed.lime_local_get_iff (stack := stack) (rest := code ops) found).mp inside
      exact ⟨⟨bytes, .source (stack ++ [v]) ops, labels⟩, .get found,
        by simp [render, Phase.renderCode, Phase.renderIn, List.append_assoc, values]⟩
    | drop =>
      obtain ⟨savedTypes, type, split, _⟩ := checked_drop ready.2.1
      obtain ⟨kept, dropped, rfl, _, droppedType⟩ := List.map_eq_append_iff.mp split
      obtain ⟨v, rest, rfl, _, restNil⟩ := List.map_eq_cons_iff.mp droppedType
      obtain rfl := List.map_eq_nil_iff.mp restNil
      obtain rfl := (Computed.lime_drop_iff (stack := kept) (v := v) (rest := code ops)).mp inside
      exact ⟨⟨bytes, .source kept ops, labels⟩, .drop, rfl⟩
    | call i site =>
      obtain ⟨_, split, resolved, _, _⟩ := checked_call ready.2.1
      obtain ⟨saved, args, rfl, _, typed⟩ := List.map_eq_append_iff.mp split
      obtain rfl := (Computed.lime_direct_call_iff (stack := saved ++ args) (tail := code ops) resolved).mp inside
      exact ⟨⟨bytes, .invoke saved site args ops, labels⟩, .resolve typed,
        by simp [render, Phase.renderCode, Phase.renderIn, plug_invoke, List.append_assoc]⟩
    | callIndirect indirect =>
      obtain ⟨_, stackTyped, linked, _⟩ := checked_indirect ready.2.1
      obtain ⟨operands, selector, rfl, operandsTyped⟩ := i32_suffix stackTyped
      obtain ⟨saved, args, rfl, _, typed⟩ := List.map_eq_append_iff.mp operandsTyped
      obtain ⟨target, found, rfl⟩ := (IndirectSite.step_iff (memory := mem) (stack := saved ++ args)
        (selector := selector) (rest := code ops) linked).mp inside
      exact ⟨_, .callIndirect typed found, render_lookup.symm⟩
    | br depth => exact (branch ⟨depth, rfl⟩).elim
    | brIf depth =>
      obtain ⟨_, _, typed, _, _⟩ := checked_brIf ready.2.1
      obtain ⟨operands, guard, rfl, _⟩ := i32_suffix typed
      have taken := (Computed.lime_br_if_iff (saved := operands) (condition := guard)
        (depth := depth) (rest := code ops)).mp inside
      refine ⟨_, .brIf, ?_⟩
      cases taken
      by_cases zero : guard = 0
      · simp only [render, Phase.renderCode, Phase.renderIn, ite_eq_left zero, List.append_nil]
      · simp only [render, Phase.renderCode, Phase.renderIn, Phase.branch, code, expr, Op.instr, expression,
          List.map_cons, ite_eq_right zero, List.append_assoc, List.singleton_append]
    | brTable depths fallback =>
      obtain ⟨_, _, typed, _, _⟩ := checked_brTable ready.2.1
      obtain ⟨operands, selector, rfl, _⟩ := i32_suffix typed
      obtain rfl := (Computed.lime_br_table_iff (saved := operands) (selector := selector)
        (depths := depths) (fallback := fallback) (rest := code ops)).mp inside
      exact ⟨_, .brTable, rfl⟩
    | loop type body =>
      obtain ⟨_, split, resolved, _, _⟩ := checked_loop ready.2.1
      obtain ⟨saved, args, rfl, _, typed⟩ := List.map_eq_append_iff.mp split
      obtain rfl := (loop_step resolved typed).mp inside
      exact ⟨_, .loop typed, by
        simp only [render, Phase.renderCode, Phase.renderIn, scopeFor, labelBranchTypes, labelContinuation,
          Label.branchTypes, Label.continuation, framed, List.append_assoc, List.singleton_append]⟩
    | if_ type left right =>
      obtain ⟨_, typed, _, _, _, _⟩ := checked_if ready.2.1
      obtain ⟨operands, guard, rfl, operandsTyped⟩ := i32_suffix typed
      obtain ⟨saved, args, rfl, _, argsTyped⟩ := List.map_eq_append_iff.mp operandsTyped
      have taken := (Computed.lime_if_iff (saved := saved ++ args) (condition := guard) (bt := type.blockType)
        (thenBody := expr left) (elseBody := expr right) (rest := code ops)).mp inside
      refine ⟨⟨bytes, .block ⟨type, saved, ops, none⟩ args (select guard left right), labels⟩, .if_ argsTyped, ?_⟩
      have blockCode :
          (if guard = 0 then expr right else expr left) = expr (select guard left right) := by
        by_cases zero : guard = (0 : BitVec 32)
        · have chosen : select guard left right = right := ite_eq_left zero
          rw [ite_eq_left zero, chosen]
        · have chosen : select guard left right = left := ite_eq_right zero
          rw [ite_eq_right zero, chosen]
      rw [blockCode] at taken
      cases taken
      rfl

private theorem block_step {label : Label H} {args : List Value} {arm : List (Op H)}
    (resolved : label.type.Resolved active.module)
    (typed : args.map Value.type = label.type.signature.params) :
    Internal ⟨mem.store bytes, active, values (label.saved ++ args) ++
      .source (.block label.type.blockType (expr arm)) :: code label.tail⟩ dst ↔
      dst = ⟨mem.store bytes, active, values label.saved ++
        .label label.type.signature.results.length [] (values args ++ code arm) :: code label.tail⟩ := by
  have arity : args.length = label.type.signature.params.length := by
    simpa using congrArg List.length typed
  change Step CallFrame.limeNoHost _ _ ↔ _
  rw [Computed.lime_block_step_iff]
  constructor
  · rintro ⟨saved, used, signature, split, lookup, size, rfl⟩
    change blockType? active.module.types label.type.blockType = some label.type.signature at resolved
    rw [resolved] at lookup
    cases lookup
    obtain ⟨rfl, rfl⟩ := List.append_inj' split (arity.trans size.symm)
    rfl
  · intro same
    exact ⟨label.saved, args, label.type.signature, rfl, resolved, arity, same⟩

private theorem block_read {label : Label H} {args : List Value} {arm : List (Op H)}
    (ready : Ready mem host active results (.block label args arm) labels)
    (move : Internal (render mem outer active results ⟨bytes, .block label args arm, labels⟩) dst) :
    ∃ next, Edge mem host active results ⟨bytes, .block label args arm, labels⟩ next ∧
      dst = render mem outer active results next := by
  have stays (out : List Admin) :
      ¬ PureStep active.module.types [.label (labelBranchTypes results labels).length (labelContinuation labels) (values (label.saved ++ args) ++
        .source (.block label.type.blockType (expr arm)) :: code label.tail)] out :=
    Computed.lime_label_stays rfl (by simp) (by simp) (by simp)
  obtain ⟨mid, inside, rfl⟩ := underLabel stays move
  obtain rfl := (block_step ready.2.2.1 ready.2.2.2.1).mp inside
  exact ⟨⟨bytes, .source args arm, label :: labels⟩, .block ready.2.1, by
    simp only [render, Phase.renderCode, Phase.renderIn, scopeFor, labelBranchTypes, labelContinuation,
      Label.branchTypes, Label.continuation, ready.2.1, framed, List.append_assoc, List.singleton_append]⟩

private theorem trap_read {stack : List Value} {rest : List Admin}
    (move : Internal (render mem outer active results ⟨bytes, .trapped stack rest, labels⟩) dst) :
    ∃ next, Edge mem host active results ⟨bytes, .trapped stack rest, labels⟩ next ∧
      dst = render mem outer active results next := by
  by_cases someCode : stack ≠ [] ∨ rest ≠ []
  · have stays (out : List Admin) :
        ¬ PureStep active.module.types [.label (labelBranchTypes results labels).length (labelContinuation labels) (values stack ++ .trap :: rest)] out :=
      Computed.lime_label_stays rfl (by simp) (by simp) (fun _ => someCode)
    obtain ⟨mid, inside, rfl⟩ := underLabel stays move
    have erase := Computed.lime_trap_front_iff (s := mem.store bytes) (f := active) (dst := mid)
      (stack := stack) (tail := rest)
    obtain ⟨kept, removed, cut, next, split, suffix, activeTrap, rfl⟩ := erase.mp inside
    exact ⟨⟨bytes, .trapped kept next, labels⟩, .erase split suffix activeTrap, rfl⟩
  · obtain ⟨emptyStack, emptyRest⟩ := not_or.mp someCode
    have stackNil : stack = [] := not_not.mp emptyStack
    have restNil : rest = [] := not_not.mp emptyRest
    subst stack rest
    have exit := closeLabel (r := .trap) move
    cases labels with
    | nil => exact ⟨⟨bytes, .frameResult .trap, []⟩, .labelTrap, exit⟩
    | cons label rest =>
      exact ⟨⟨bytes, .trapped label.saved (code label.tail), rest⟩, .armTrap,
        by simpa [render, Phase.renderCode, Phase.renderIn, framed, scopeFor, result, List.append_assoc] using exit⟩

private theorem frame_read {r : Result}
    (move : Internal (render mem outer active results ⟨bytes, .frameResult r, []⟩) dst) :
    dst = render mem outer active results ⟨bytes, .done r, []⟩ := by
  cases r with
  | values vs => exact Nested.lime_frame_result (r := .values vs) move
  | trap => exact Nested.lime_frame_result (r := .trap) move

private theorem read {a : State H} (ready : Ready mem host active results a.phase a.labels) (live : mem.Live a.bytes)
    (move : Step host (render mem outer active results a) dst) :
    ∃ next, Edge mem host active results a next ∧ dst = render mem outer active results next := by
  rcases a with ⟨bytes, phase, labels⟩
  cases phase with
  | source stack ops =>
    have absent : decompose? (render mem outer active results ⟨bytes, .source stack ops, labels⟩) = none :=
      noLabelCallout (by
        cases ops with
        | nil => simp [code, expr, expression]
        | cons op ops => cases op <;> simp [code, expr, Op.instr, expression, asValue?])
    exact source_read ready ((withoutCallout absent).mp move)
  | block label args arm =>
    have absent : decompose? (render mem outer active results ⟨bytes, .block label args arm, labels⟩) = none :=
      noLabelCallout (by simp [asValue?])
    exact block_read ready ((withoutCallout absent).mp move)
  | invoke saved site args ops => exact invoke_read ready live move
  | wasm _ _ _ _ _ => exact wasm_read ready move
  | memory _ _ _ _ => exact memory_read ready live move
  | trapped stack rest =>
    have absent : decompose? (render mem outer active results ⟨bytes, .trapped stack rest, labels⟩) = none :=
      noLabelCallout (by simp)
    exact trap_read ((withoutCallout absent).mp move)
  | frameResult out =>
    have noLabels : labels = [] := ready.2.1
    subst labels
    have absent : decompose? (render mem outer active results ⟨bytes, .frameResult out, []⟩) = none := by
      cases out <;> simp [decompose?, render, Phase.renderCode, Phase.renderIn, scopeFor, framed, result]
    exact ⟨⟨bytes, .done out, []⟩, .frameDone, frame_read ((withoutCallout absent).mp move)⟩
  | done out =>
    have absent : decompose? (render mem outer active results ⟨bytes, .done out, labels⟩) = none := by
      cases out <;> simp [decompose?, render, Phase.renderCode, Phase.renderIn, result]
    have internal := (withoutCallout absent).mp move
    cases out with
    | values vs => exact (Nested.lime_result_stuck (r := .values vs) internal).elim
    | trap => exact (Nested.lime_result_stuck (r := .trap) internal).elim

private theorem sound {a b : State H} (ready : Ready mem host active results a.phase a.labels) (live : mem.Live a.bytes)
    (edge : Edge mem host active results a b) :
    Step host (render mem outer active results a) (render mem outer active results b) := by
  cases edge with
  | @get bytes stack index v ops labels found =>
    have get := (Computed.lime_local_get_iff (s := mem.store bytes) (stack := stack) (rest := code ops) found).mpr rfl
    have move := framed_step (scope := (scopeFor results labels)) (outer := outer) (.label get (labelBranchTypes results labels).length (labelContinuation labels))
    apply Step.of_internal
    change Step CallFrame.limeNoHost _ _
    simpa [render, Phase.renderCode, Phase.renderIn, code, expr, Op.instr, expression, values, List.append_assoc] using move
  | @drop bytes stack v ops labels =>
    have drop := (Computed.lime_drop_iff (s := mem.store bytes) (f := active) (stack := stack)
      (v := v) (rest := code ops)).mpr rfl
    exact Step.of_internal (framed_step (.label drop (labelBranchTypes results labels).length (labelContinuation labels)))
  | @brIf bytes stack guard depth ops labels =>
    have branch := (Computed.lime_br_if_iff (s := mem.store bytes) (f := active)
      (saved := stack) (condition := guard) (depth := depth) (rest := code ops)).mpr rfl
    have move := framed_step (outer := outer) (scope := scopeFor results labels)
      (.label branch (labelBranchTypes results labels).length (labelContinuation labels))
    apply Step.of_internal
    change Step CallFrame.limeNoHost _ _
    by_cases zero : guard = 0
    · simpa only [render, Phase.renderCode, Phase.renderIn, code, expr, Op.instr, expression,
        List.map_cons, ite_eq_left zero, List.append_nil] using move
    · simpa only [render, Phase.renderCode, Phase.renderIn, Phase.branch, code, expr, Op.instr, expression,
        List.map_cons, ite_eq_right zero, List.append_assoc, List.singleton_append] using move
  | @brTable bytes stack selector depths fallback ops labels =>
    have branch := (Computed.lime_br_table_iff (s := mem.store bytes) (f := active)
      (saved := stack) (selector := selector) (depths := depths) (fallback := fallback) (rest := code ops)).mpr rfl
    exact Step.of_internal (framed_step (.label branch (labelBranchTypes results labels).length (labelContinuation labels)))
  | @branchLower bytes stack depth ops label labels positive =>
    have lower : Step host ⟨mem.store bytes, active, [.label label.branchTypes.length label.continuation
        (values stack ++ .source (.br depth) :: code ops)]⟩
        ⟨mem.store bytes, active, values stack ++ [.source (.br (lowerLabel depth))]⟩ :=
      BranchExit.lime_label_br_cont_iff.mpr (.inr ⟨positive, rfl⟩)
    have move := framed_step (outer := outer) (scope := scopeFor results (label :: labels)) lower
    simpa only [render, Phase.renderCode, Phase.renderIn, Phase.branch, labelBranchTypes, labelContinuation,
      scopeFor, framed, values_append, code, expr, Op.instr, expression, List.map_cons,
      List.append_assoc, List.singleton_append] using move
  | @branchDeliver bytes scratch payload depth ops label labels zero exits typed =>
    have arity : payload.length = label.branchTypes.length := by
      simpa [Label.branchTypes, exits] using congrArg List.length typed
    have deliver : Step host ⟨mem.store bytes, active, [.label label.branchTypes.length label.continuation
        (values (scratch ++ payload) ++ .source (.br depth) :: code ops)]⟩
        ⟨mem.store bytes, active, values payload⟩ :=
      BranchExit.lime_label_br_cont_iff.mpr (.inl ⟨scratch, payload, rfl, arity, zero,
        by simp [Label.continuation, exits, expression]⟩)
    have move := framed_step (outer := outer) (scope := scopeFor results (label :: labels)) deliver
    simpa only [render, Phase.renderCode, Phase.renderIn, Phase.branch, labelBranchTypes, labelContinuation,
      scopeFor, framed, code, expr, Op.instr, expression, List.map_cons, values_append] using move
  | @branchRestart bytes scratch args depth ops label body labels zero loopBody typed =>
    have arity : args.length = label.branchTypes.length := by
      simpa [Label.branchTypes, loopBody] using congrArg List.length typed
    have restart : Step host ⟨mem.store bytes, active, [.label label.branchTypes.length label.continuation
        (values (scratch ++ args) ++ .source (.br depth) :: code ops)]⟩
        ⟨mem.store bytes, active, values args ++ expression label.continuation⟩ :=
      BranchExit.lime_label_br_cont_iff.mpr (.inl ⟨scratch, args, rfl, arity, zero, rfl⟩)
    have move := framed_step (outer := outer) (scope := scopeFor results (label :: labels)) restart
    simpa [render, Phase.renderCode, Phase.renderIn, Phase.branch, labelBranchTypes, labelContinuation,
      scopeFor, framed, Label.continuation, loopBody, code, expr, Op.instr, expression, List.append_assoc] using move
  | @functionBranch bytes scratch payload depth ops zero typed =>
    have arity : payload.length = results.length := by
      simpa using congrArg List.length typed
    have deliver : Step host ⟨mem.store bytes, active, [.label results.length []
        (values (scratch ++ payload) ++ .source (.br depth) :: code ops)]⟩
        ⟨mem.store bytes, active, values payload⟩ :=
      BranchExit.lime_label_br_iff.mpr (.inl ⟨scratch, payload, rfl, arity, zero, rfl⟩)
    exact .frame deliver results.length outer
  | @if_ bytes saved args guard type left right ops labels _ =>
    have branch : Internal ⟨mem.store bytes, active, values ((saved ++ args) ++ [Value.int .i32 guard]) ++
        .source (.if_ type.blockType (expr left) (expr right)) :: code ops⟩
        ⟨mem.store bytes, active, values (saved ++ args) ++ .source (.block type.blockType (expr (select guard left right))) :: code ops⟩ := by
      apply (Computed.lime_if_iff (saved := saved ++ args) (condition := guard) (bt := type.blockType)
        (thenBody := expr left) (elseBody := expr right) (rest := code ops)).mpr
      by_cases zero : guard = (0 : BitVec 32)
      · have chosen : select guard left right = right := ite_eq_left zero
        rw [ite_eq_left zero, chosen]
      · have chosen : select guard left right = left := ite_eq_right zero
        rw [ite_eq_right zero, chosen]
    exact Step.of_internal (framed_step (.label branch (labelBranchTypes results labels).length (labelContinuation labels)))
  | @block bytes label args arm labels exits =>
    have block := (block_step (mem := mem) (bytes := bytes) (arm := arm) ready.2.2.1 ready.2.2.2.1).mpr rfl
    have move := framed_step (scope := scopeFor results labels) (outer := outer)
      (.label block (labelBranchTypes results labels).length (labelContinuation labels))
    apply Step.of_internal
    change Step Execution.Runtime.noHostCalls _ _
    simpa only [render, Phase.renderCode, Phase.renderIn, scopeFor, labelBranchTypes, labelContinuation, framed,
      Label.branchTypes, Label.continuation, exits, List.append_assoc, List.singleton_append] using move
  | @loop bytes saved args type body ops labels typed =>
    obtain ⟨_, _, resolved, _, _⟩ := checked_loop ready.2.1
    have enter := (loop_step (mem := mem) (bytes := bytes) (body := body) (ops := ops)
      (saved := saved) resolved typed).mpr rfl
    have move := framed_step (scope := scopeFor results labels) (outer := outer)
      (.label enter (labelBranchTypes results labels).length (labelContinuation labels))
    apply Step.of_internal
    change Step Execution.Runtime.noHostCalls _ _
    simpa only [render, Phase.renderCode, Phase.renderIn, scopeFor, labelBranchTypes, labelContinuation,
      Label.branchTypes, Label.continuation, framed, code, expr, Op.instr, expression, List.map_cons,
      List.append_assoc, List.singleton_append] using move
  | @resolve bytes saved args index site ops labels typed =>
    obtain ⟨_, _, resolved, _, _⟩ := checked_call ready.2.1
    have call := (Computed.lime_direct_call_iff (s := mem.store bytes) (stack := saved ++ args)
      (tail := code ops) resolved).mpr rfl
    have move := framed_step (scope := (scopeFor results labels)) (outer := outer) (.label call (labelBranchTypes results labels).length (labelContinuation labels))
    apply Step.of_internal
    change Step CallFrame.limeNoHost _ _
    simpa [render, Phase.renderCode, Phase.renderIn, plug_invoke, code, expr, Op.instr, expression, List.append_assoc, values] using move
  | @callIndirect bytes saved args selector indirect target ops labels _ found =>
    obtain ⟨_, _, linked, _⟩ := checked_indirect ready.2.1
    have lookup := (IndirectSite.step_iff (memory := mem) (bytes := bytes) (stack := saved ++ args)
      (selector := selector) (rest := code ops) linked).mpr ⟨target, found, rfl⟩
    rw [render_lookup]
    exact Step.of_internal (framed_step (.label lookup (labelBranchTypes results labels).length
      (labelContinuation labels)))
  | @wasm bytes saved site callee phase next ops labels edge =>
    obtain ⟨_, linked, found, _, notCall, notDone, admitted, _, _⟩ := ready
    have allocated : site.graph.LimeAllocated (mem.store bytes) := linked.graphAllocated
    have inner := (wasm_step_iff (active := active) (saved := saved) (rest := code ops) (s := mem.store bytes)
      linked.graphChecked allocated found admitted notCall notDone).mpr ⟨next, edge, rfl⟩
    rw [render_wasm]
    exact Step.of_internal (framed_step (.label inner (labelBranchTypes results labels).length
      (labelContinuation labels)))
  | @memory bytes written saved callee phase next ops labels edge =>
    obtain ⟨_, allocated, checked, notDone, admitted, _, _⟩ := ready
    have inner := (MemoryCallee.step_iff (caller := active) (saved := saved) (tail := code ops)
      checked allocated admitted live notDone).mpr ⟨written, next, edge, rfl⟩
    rw [render_memory]
    exact Step.of_internal (framed_step (.label inner (labelBranchTypes results labels).length
      (labelContinuation labels)))
  | @returned bytes next saved site args ops vs labels _ _ answer =>
    have atHost := located (mem := mem) (labels := labels) (results := results) (outer := outer) (active := active)
      (bytes := bytes) (saved := saved) (ops := ops) ready.2.1 ready.2.2.1
    have move := Step.callout_returned atHost answer
    simpa [resume, render, Phase.renderCode, Phase.renderIn, Site.callout,
      Execution.Runtime.Callout.fill, plug_invoke, result, List.append_assoc] using move
  | @trapped bytes next saved site args ops labels _ answer =>
    have atHost := located (mem := mem) (labels := labels) (results := results) (outer := outer) (active := active)
      (bytes := bytes) (saved := saved) (ops := ops) ready.2.1 ready.2.2.1
    have move := Step.callout_returned atHost answer
    simpa [resume, render, Phase.renderCode, Phase.renderIn, Site.callout, Execution.Runtime.Callout.fill, plug_invoke, result] using move
  | @diverged bytes saved site args ops labels answer => exact Step.callout_diverged (located (labels := labels) (results := results) ready.2.1 ready.2.2.1) answer
  | @erase bytes stack kept removed before cut rest labels split suffix activeTrap =>
    have move : Internal ⟨mem.store bytes, active, values stack ++ .trap :: before⟩
        ⟨mem.store bytes, active, values kept ++ .trap :: rest⟩ :=
      Computed.lime_trap_front_iff.mpr ⟨kept, removed, cut, rest, split, suffix, activeTrap, rfl⟩
    exact Step.of_internal (framed_step (.label move (labelBranchTypes results labels).length (labelContinuation labels)))
  | @armTrap bytes label labels =>
    have move := framed_step (scope := scopeFor results (label :: labels)) (outer := outer)
      (.pure (host := host) (mem.store bytes) active (.labelTrap label.branchTypes.length label.continuation))
    simpa [render, Phase.renderCode, Phase.renderIn, labelBranchTypes, labelContinuation, scopeFor, framed, values, List.append_assoc] using move
  | @armResult bytes stack label labels =>
    have move := framed_step (scope := scopeFor results (label :: labels)) (outer := outer)
      (.pure (host := host) (mem.store bytes) active (.labelDone label.branchTypes.length label.continuation stack))
    simpa [render, Phase.renderCode, Phase.renderIn, labelBranchTypes, labelContinuation, scopeFor, framed, code, expr, expression,
      List.append_assoc] using move
  | labelTrap => exact .frame (.pure _ _ (.labelTrap results.length [])) results.length outer
  | @labelResult bytes stack =>
    have move := Step.frame (.pure (host := host) (mem.store bytes) active (.labelDone results.length [] stack))
      results.length outer
    simpa [render, Phase.renderCode, Phase.renderIn, scopeFor, labelBranchTypes, labelContinuation, framed, code, expr, expression, result]
      using move
  | @frameDone _ out =>
    cases out with
    | trap => exact .pure _ _ (.frameTrap _ active)
    | values vs =>
      exact .pure _ _ (.frameDone _ active vs (by simpa using congrArg List.length ready.2.2))

theorem step_iff {a : State H} (ready : Ready mem host active results a.phase a.labels) (live : mem.Live a.bytes) :
    Step host (render mem outer active results a) dst ↔
      ∃ next, Edge mem host active results a next ∧ dst = render mem outer active results next := by
  refine ⟨read ready live, ?_⟩
  rintro ⟨_, edge, rfl⟩
  exact sound ready live edge

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs
