module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs

open Execution.Runtime (AdminInstr Frame Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall.Ranked
open CallContinuation.OuterCall (CallTarget)

set_option backward.isDefEq.respectTransparency false

private theorem source_emit (op : Graph.Op) : ∃ instr, Graph.limeEmit op = .source instr := by
  cases op with
  | numeric op => cases op <;> exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

private theorem emitted_absent {H : Type} (s : Store H) (ops : List Graph.Op) (acc : List Value) :
    Execution.Runtime.decomposeFrom? coding s acc (ops.map Graph.limeEmit) = none := by
  induction ops generalizing acc with
  | nil => rfl
  | cons op rest ih =>
    obtain ⟨instr, emit⟩ := source_emit op
    rw [List.map_cons, emit, decomposeFrom?_source_cons]
    cases asValue? (.source instr) <;> simp [ih]

private theorem graph_body_absent {H : Type} {s : Store H} {graph : Graph.Program}
    (allocated : graph.LimeAllocated s) {fn fallthrough enclosing phase kind}
    (ready : Graph.AdmittedAt graph fn fallthrough enclosing phase kind) :
    match phase with
    | .label _ body => Execution.Runtime.decomposeFrom? coding s [] (body.render Graph.limeAdmin) = none
    | _ => True := by
  induction ready with
  | running _ _ =>
    simp only [Graph.Body.render, Graph.limeAdmin, decomposeFrom?_values_append]
    exact emitted_absent s _ _
  | @active fn fallthrough enclosing kind locals saved target child rest callee _ _ found _ live _ _ ih =>
    have allocation := allocated target.address callee found
    cases child with
    | invoke args =>
      simp [Graph.Body.render, Graph.Phase.renderAt, Graph.limeAdmin, List.append_assoc,
        decomposeFrom?_invoke_cons, Execution.Runtime.decomposeHead?, allocation]
    | label locals body =>
      simp [Graph.limeAdmin] at ih
      simp [Graph.Body.render, Graph.Phase.renderAt, Graph.limeAdmin, List.append_assoc, ih]
    | returning locals stack =>
      simp [Graph.Body.render, Graph.Phase.renderAt, Graph.limeAdmin, List.append_assoc, asValue?]
    | exit locals out =>
      cases out <;> simp [Graph.Body.render, Graph.Phase.renderAt, Graph.limeAdmin,
        List.append_assoc, CallContinuation.Nested.resultCode]
    | _ => exact live.elim
  | block _ _ ih | indexedBlock _ _ ih | loop _ _ _ ih | indexedLoop _ _ _ _ ih =>
    simp [Graph.limeAdmin] at ih
    simp [Graph.Body.render, Graph.limeAdmin, ih]
  | trapped _ =>
    simp [Graph.Body.render, Graph.limeAdmin]
  | _ => trivial

theorem wasm_absent {H : Type} {s : Store H} {graph : Graph.Program} {callee : WasmTarget}
    (allocated : graph.LimeAllocated s) (found : graph.lookup callee.address = some callee.fn)
    {phase : Graph.Phase} (ready : Graph.Admitted graph callee.fn phase)
    (saved : List Value) (rest : List Admin) (notCall : ∀ args, phase ≠ .call args)
    (notDone : ∀ out, phase ≠ .done out) :
    Execution.Runtime.decomposeFrom? coding s []
      (values saved ++ phase.render Graph.limeAdmin callee.callTarget ++ rest) = none := by
  have allocation := allocated callee.address callee.fn found
  cases phase with
  | call args => exact (notCall args rfl).elim
  | done out => exact (notDone out rfl).elim
  | label locals body =>
    have absent := graph_body_absent allocated ready
    simp [Graph.limeAdmin] at absent
    simp [Graph.Phase.render, Graph.Phase.renderAt, Graph.limeAdmin, List.append_assoc, absent]
  | invoke args =>
    simp [Graph.Phase.render, Graph.Phase.renderAt, Graph.limeAdmin, WasmTarget.callTarget,
      List.append_assoc, decomposeFrom?_invoke_cons, Execution.Runtime.decomposeHead?, allocation]
  | branching | returning | restart | indexedRestart =>
    simp [Graph.Phase.render, Graph.Phase.renderAt, Graph.limeAdmin, Graph.limeEmit, Graph.Op.emit,
      Graph.limeCodeSyntax, List.append_assoc, asValue?]
  | exit locals out =>
    cases out <;> simp [Graph.Phase.render, Graph.Phase.renderAt, Graph.limeAdmin,
      List.append_assoc, CallContinuation.Nested.resultCode]

private theorem wasm_shape (callee : WasmTarget) (phase : Graph.Phase)
    (notCall : ∀ args, phase ≠ .call args) (notDone : ∀ out, phase ≠ .done out) :
    (∃ args, phase = .invoke args) ∨
      ∃ n frame body, phase.render Graph.limeAdmin callee.callTarget = [.frame n frame body] := by
  cases phase with
  | call args => exact (notCall args rfl).elim
  | done out => exact (notDone out rfl).elim
  | invoke args => exact .inl ⟨args, rfl⟩
  | _ => exact .inr ⟨_, _, _, rfl⟩

theorem wasm_stays (callee : WasmTarget) {phase : Graph.Phase}
    (notCall : ∀ args, phase ≠ .call args) (notDone : ∀ out, phase ≠ .done out)
    {types : List Wasm.Lime1.FuncType} {n : Nat} {cont : Wasm.Lime1.Expr}
    {saved : List Value} {rest out : List Admin} :
    ¬ PureStep types [.label n cont (values saved ++ phase.render Graph.limeAdmin callee.callTarget ++ rest)] out := by
  rcases wasm_shape callee phase notCall notDone with ⟨args, rfl⟩ | ⟨arity, frame, body, code⟩
  · simpa only [Graph.Phase.render, Graph.Phase.renderAt, Graph.limeAdmin, WasmTarget.callTarget,
      values_append, List.append_assoc, List.singleton_append] using
      (CallContinuation.OuterCall.Computed.lime_label_stays (types := types) (n := n) (cont := cont)
        (stack := saved ++ args) (head := .invoke callee.address) (rest := rest) (out := out)
        rfl (by simp) (by simp) (by simp))
  · simpa only [code, List.append_assoc, List.singleton_append] using
      (CallContinuation.OuterCall.Computed.lime_label_stays (types := types) (n := n) (cont := cont)
        (stack := saved) (head := .frame arity frame body) (rest := rest) (out := out)
        rfl (by simp) (by simp) (by simp))

theorem wasm_step_iff {H : Type} {s : Store H} {graph : Graph.Program} {callee : WasmTarget}
    {active : Frame} {phase : Graph.Phase} {saved : List Value} {rest : List Admin} {dst : Config H}
    (checked : graph.checkDirect = true) (allocated : graph.LimeAllocated s)
    (found : graph.lookup callee.address = some callee.fn) (ready : Graph.Admitted graph callee.fn phase)
    (notCall : ∀ args, phase ≠ .call args) (notDone : ∀ out, phase ≠ .done out) :
    Internal ⟨s, active, values saved ++ phase.render Graph.limeAdmin callee.callTarget ++ rest⟩ dst ↔
      ∃ next, graph.FrameEdge callee.address phase next ∧
        dst = ⟨s, active, values saved ++ next.render Graph.limeAdmin callee.callTarget ++ rest⟩ := by
  have exactStep {mid} := Graph.lime_resolved_frame_step_iff (s := s) (caller := active)
    (target := callee.callTarget) (b := mid) checked allocated found rfl ready notCall
  constructor
  · intro move
    change Step CallFrame.limeNoHost _ _ at move
    have localStep : ∃ mid, Step CallFrame.limeNoHost (Graph.limeConfig s active callee.callTarget phase) mid ∧
        dst = ⟨mid.store, mid.frame, values saved ++ mid.code ++ rest⟩ := by
      rcases wasm_shape callee phase notCall notDone with ⟨args, rfl⟩ | ⟨arity, frame, body, code⟩
      · have allocation := allocated callee.address callee.fn found
        have count : args.length = callee.fn.declaration.type.params.length := by
          change args.length = callee.fn.declaration.params.length
          cases ready with
          | invoke typed => simpa using congrArg List.length typed
        obtain ⟨mid, invoke, rfl⟩ := CallContinuation.lime_invoke_strip_suffix
          (stack := saved ++ args) (rest := rest) (a := callee.address) (by
            simpa only [Graph.Phase.render, Graph.Phase.renderAt, Graph.limeAdmin, WasmTarget.callTarget,
              values_append, List.append_assoc, List.singleton_append] using move)
        have pushed := (CallFrame.lime_invoke_wasm_prefix_iff (saved := saved) (args := args) allocation count).mp invoke
        cases pushed
        refine ⟨_, (CallFrame.lime_invoke_wasm_exact allocation count).mpr rfl, ?_⟩
        rfl
      · obtain ⟨mid, inner, eq⟩ := CallContinuation.lime_frame_context_inv (saved := saved)
          (rest := rest) (inside := frame) (n := arity) (code := body) (by
            simpa only [code, List.append_assoc, List.singleton_append] using move)
        exact ⟨mid, by simpa only [Graph.limeConfig, code] using inner, eq⟩
    obtain ⟨mid, inner, rfl⟩ := localStep
    obtain ⟨next, edge, rfl⟩ := exactStep.mp inner
    exact ⟨next, edge, rfl⟩
  · rintro ⟨next, edge, rfl⟩
    have inner := exactStep.mpr ⟨next, edge, rfl⟩
    exact Step.context inner saved rest

private theorem afterBlock_not_call {phase : Graph.Phase} (notCall : ∀ args, phase ≠ .call args)
    (saved : List Value) (result : Option NumType) (rest : List Graph.Op) (kind : Graph.LabelKind) :
    ∀ args, phase.afterBlock saved result rest kind ≠ .call args := by
  cases phase <;> simp_all [Graph.Phase.afterBlock]
  split <;> simp

private theorem branchHere_not_call (kind : Graph.LabelKind) (locals values : List Value) :
    ∀ args, kind.branchHere locals values ≠ .call args := by
  cases kind <;> simp [Graph.LabelKind.branchHere]

private theorem layer_not_call {fn : Graph.Function} {steps : CallTarget → Graph.Phase → Graph.Phase → Prop}
    {phase next : Graph.Phase} {kind : Graph.LabelKind} (move : Graph.Layer fn steps phase next kind) :
    ∀ args, next ≠ .call args := by
  induction move <;> try solve | simp
  case blockStep ih => exact afterBlock_not_call ih _ _ _ _
  case indexedBlockStep ih => exact afterBlock_not_call ih _ _ _ _
  case loopStep ih => exact afterBlock_not_call ih _ _ _ _
  case indexedLoopStep ih => exact afterBlock_not_call ih _ _ _ _
  case branchHere => exact branchHere_not_call _ _ _

theorem wasm_next_not_call {graph : Graph.Program} {callee : WasmTarget} {phase next : Graph.Phase}
    (found : graph.lookup callee.address = some callee.fn) (move : graph.FrameEdge callee.address phase next) :
    ∀ args, next ≠ .call args :=
  layer_not_call ((graph.frameEdge_iff found).mp move)

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs
