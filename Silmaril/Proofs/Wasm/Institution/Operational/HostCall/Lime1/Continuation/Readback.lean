module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Preservation
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Context
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Thms
import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs

open Execution.Runtime (EvalCtx Frame Result Value)
open Wasm.Lime1.Execution
open CallContinuation
open CallContinuation.OuterCall

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
    (stays : ∀ out, ¬ PureStep active.module.types [.label (labelResults results labels).length [] body] out)
    (move : Internal ⟨mem.store bytes, outer, framed active [.label (labelResults results labels).length [] body] (scopeFor results labels)⟩ dst) :
    ∃ mid, Internal ⟨mem.store bytes, active, body⟩ mid ∧ dst =
      ⟨mid.store, outer, framed mid.frame [.label (labelResults results labels).length [] mid.code] (scopeFor results labels)⟩ := by
  rcases body_cases move with inside | ⟨out, exiting, _⟩
  · exact inside
  · exact (stays out exiting).elim

private theorem closeLabel {r : Result}
    (move : Internal ⟨mem.store bytes, outer, framed active [.label (labelResults results labels).length [] (result r)] (scopeFor results labels)⟩ dst) :
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
      (site.callout (invokeContext (scopeFor results labels) (labelResults results labels).length active saved ops) args) :=
  ⟨rfl, allocated, by simpa [Site.callout] using congrArg List.length typed⟩

private theorem invoke_read {saved args : List Value} {site : Site H} {ops : List (Op H)}
    (ready : Ready mem host active results (.invoke saved site args ops) labels) (live : mem.Live bytes)
    (move : Step host (render mem outer active results ⟨bytes, .invoke saved site args ops, labels⟩) dst) :
    ∃ next, Edge mem host active results ⟨bytes, .invoke saved site args ops, labels⟩ next ∧
      dst = render mem outer active results next := by
  obtain ⟨_, allocated, typed, contract, _, _⟩ := ready
  have exactStep := Site.step_iff (dst := dst) (outer := outer)
    (context := invokeContext (scopeFor results labels) (labelResults results labels).length active saved ops) allocated contract live typed
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
  · rcases BranchExit.lime_label_br_iff.mp (Step.pure (host := host) (mem.store bytes) active pop) with
      ⟨scratch, used, split, arity, zero, native⟩ | ⟨positive, native⟩
    · have first : (targetTypes results labels)[0]? = some (labelResults results labels) := by
        cases labels <;> rfl
      rw [zero, first] at target
      cases target
      obtain ⟨_, payload, typedSplit, _, payloadTyped⟩ := List.map_eq_append_iff.mp typed
      have size : payload.length = (labelResults results labels).length := by
        simpa using congrArg List.length payloadTyped
      have same := (List.append_inj' (split.symm.trans typedSplit) (arity.trans size.symm)).2
      subst used
      rw [typedSplit]
      cases native
      cases labels with
      | nil => exact ⟨_, .functionBranch zero payloadTyped, rfl⟩
      | cons label labels =>
        exact ⟨_, .branchDeliver zero payloadTyped, by
          simp only [render, Phase.renderCode, Phase.renderIn, scopeFor, framed, values_append]⟩
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

private theorem source_read {stack : List Value} {ops : List (Op H)}
    (ready : Ready mem host active results (.source stack ops) labels)
    (move : Internal (render mem outer active results ⟨bytes, .source stack ops, labels⟩) dst) :
    ∃ next, Edge mem host active results ⟨bytes, .source stack ops, labels⟩ next ∧
      dst = render mem outer active results next := by
  cases ops with
  | nil =>
    have step : Internal ⟨mem.store bytes, outer, framed active [.label (labelResults results labels).length [] (result (.values stack))] (scopeFor results labels)⟩ dst := by
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
        [.label (labelResults results labels).length [] (values stack ++ .source op.instr :: code ops)] out :=
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
    | br depth => exact (branch ⟨depth, rfl⟩).elim
    | brIf depth =>
      obtain ⟨_, _, typed, _, _⟩ := checked_brIf ready.2.1
      obtain ⟨operands, test, rfl, _, testTyped⟩ := List.map_eq_append_iff.mp typed
      obtain ⟨v, rem, rfl, vt, testEmpty⟩ := List.map_eq_cons_iff.mp testTyped
      obtain rfl := List.map_eq_nil_iff.mp testEmpty
      rcases v with ⟨vt', guard⟩
      cases vt
      have taken := (Computed.lime_br_if_iff (saved := operands) (condition := guard)
        (depth := depth) (rest := code ops)).mp inside
      refine ⟨_, .brIf, ?_⟩
      cases taken
      by_cases zero : guard = 0
      · simp only [render, Phase.renderCode, Phase.renderIn, ite_eq_left zero, List.append_nil]
      · simp only [render, Phase.renderCode, Phase.renderIn, Phase.branch, code, expr, Op.instr, expression,
          List.map_cons, ite_eq_right zero, List.append_assoc, List.singleton_append]
    | if_ type left right =>
      obtain ⟨_, typed, _, _, _, _⟩ := checked_if ready.2.1
      obtain ⟨operands, test, rfl, operandsTyped, guardTyped⟩ := List.map_eq_append_iff.mp typed
      obtain ⟨saved, args, rfl, _, argsTyped⟩ := List.map_eq_append_iff.mp operandsTyped
      obtain ⟨v, rem, rfl, vt, testEmpty⟩ := List.map_eq_cons_iff.mp guardTyped
      obtain rfl := List.map_eq_nil_iff.mp testEmpty
      rcases v with ⟨vt', guard⟩
      cases vt
      have taken := (Computed.lime_if_iff (saved := saved ++ args) (condition := guard) (bt := type.blockType)
        (thenBody := expr left) (elseBody := expr right) (rest := code ops)).mp inside
      refine ⟨⟨bytes, .block ⟨type, saved, ops⟩ args (select guard left right), labels⟩, .if_ argsTyped, ?_⟩
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
      ¬ PureStep active.module.types [.label (labelResults results labels).length [] (values (label.saved ++ args) ++
        .source (.block label.type.blockType (expr arm)) :: code label.tail)] out :=
    Computed.lime_label_stays rfl (by simp) (by simp) (by simp)
  obtain ⟨mid, inside, rfl⟩ := underLabel stays move
  obtain rfl := (block_step ready.2.1 ready.2.2.1).mp inside
  exact ⟨⟨bytes, .source args arm, label :: labels⟩, .block, by
    simp only [render, Phase.renderCode, Phase.renderIn, scopeFor, labelResults, framed,
      List.append_assoc, List.singleton_append]⟩

private theorem trap_read {stack : List Value} {rest : List Admin}
    (move : Internal (render mem outer active results ⟨bytes, .trapped stack rest, labels⟩) dst) :
    ∃ next, Edge mem host active results ⟨bytes, .trapped stack rest, labels⟩ next ∧
      dst = render mem outer active results next := by
  by_cases someCode : stack ≠ [] ∨ rest ≠ []
  · have stays (out : List Admin) :
        ¬ PureStep active.module.types [.label (labelResults results labels).length [] (values stack ++ .trap :: rest)] out :=
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

private theorem sound {a b : State H} (ready : Ready mem host active results a.phase a.labels) (edge : Edge mem host active results a b) :
    Step host (render mem outer active results a) (render mem outer active results b) := by
  cases edge with
  | @get bytes stack index v ops labels found =>
    have get := (Computed.lime_local_get_iff (s := mem.store bytes) (stack := stack) (rest := code ops) found).mpr rfl
    have move := framed_step (scope := (scopeFor results labels)) (outer := outer) (.label get (labelResults results labels).length [])
    apply Step.of_internal
    change Step CallFrame.limeNoHost _ _
    simpa [render, Phase.renderCode, Phase.renderIn, code, expr, Op.instr, expression, values, List.append_assoc] using move
  | @drop bytes stack v ops labels =>
    have drop := (Computed.lime_drop_iff (s := mem.store bytes) (f := active) (stack := stack)
      (v := v) (rest := code ops)).mpr rfl
    exact Step.of_internal (framed_step (.label drop (labelResults results labels).length []))
  | @brIf bytes stack guard depth ops labels =>
    have branch := (Computed.lime_br_if_iff (s := mem.store bytes) (f := active)
      (saved := stack) (condition := guard) (depth := depth) (rest := code ops)).mpr rfl
    have move := framed_step (outer := outer) (scope := scopeFor results labels)
      (.label branch (labelResults results labels).length [])
    apply Step.of_internal
    change Step CallFrame.limeNoHost _ _
    by_cases zero : guard = 0
    · simpa only [render, Phase.renderCode, Phase.renderIn, code, expr, Op.instr, expression,
        List.map_cons, ite_eq_left zero, List.append_nil] using move
    · simpa only [render, Phase.renderCode, Phase.renderIn, Phase.branch, code, expr, Op.instr, expression,
        List.map_cons, ite_eq_right zero, List.append_assoc, List.singleton_append] using move
  | @branchLower bytes stack depth ops label labels positive =>
    have lower : Step host ⟨mem.store bytes, active, [.label label.type.signature.results.length []
        (values stack ++ .source (.br depth) :: code ops)]⟩
        ⟨mem.store bytes, active, values stack ++ [.source (.br (lowerLabel depth))]⟩ :=
      BranchExit.lime_label_br_iff.mpr (.inr ⟨positive, rfl⟩)
    have move := framed_step (outer := outer) (scope := scopeFor results (label :: labels)) lower
    simpa only [render, Phase.renderCode, Phase.renderIn, Phase.branch, labelResults, scopeFor, framed, values_append,
      code, expr, Op.instr, expression, List.map_cons,
      List.append_assoc, List.singleton_append] using move
  | @branchDeliver bytes scratch payload depth ops label labels zero typed =>
    have arity : payload.length = label.type.signature.results.length := by
      simpa using congrArg List.length typed
    have deliver : Step host ⟨mem.store bytes, active, [.label label.type.signature.results.length []
        (values (scratch ++ payload) ++ .source (.br depth) :: code ops)]⟩
        ⟨mem.store bytes, active, values payload⟩ :=
      BranchExit.lime_label_br_iff.mpr (.inl ⟨scratch, payload, rfl, arity, zero, rfl⟩)
    have move := framed_step (outer := outer) (scope := scopeFor results (label :: labels)) deliver
    simpa only [render, Phase.renderCode, Phase.renderIn, Phase.branch, labelResults, scopeFor, framed,
      code, expr, Op.instr, expression, List.map_cons, values_append] using move
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
    exact Step.of_internal (framed_step (.label branch (labelResults results labels).length []))
  | @block bytes label args arm labels =>
    have block := (block_step (mem := mem) (bytes := bytes) (arm := arm) ready.2.1 ready.2.2.1).mpr rfl
    have move := framed_step (scope := scopeFor results labels) (outer := outer)
      (.label block (labelResults results labels).length [])
    apply Step.of_internal
    change Step Execution.Runtime.noHostCalls _ _
    simpa only [render, Phase.renderCode, Phase.renderIn, scopeFor, labelResults, framed,
      List.append_assoc, List.singleton_append] using move
  | @resolve bytes saved args index site ops labels typed =>
    obtain ⟨_, _, resolved, _, _⟩ := checked_call ready.2.1
    have call := (Computed.lime_direct_call_iff (s := mem.store bytes) (stack := saved ++ args)
      (tail := code ops) resolved).mpr rfl
    have move := framed_step (scope := (scopeFor results labels)) (outer := outer) (.label call (labelResults results labels).length [])
    apply Step.of_internal
    change Step CallFrame.limeNoHost _ _
    simpa [render, Phase.renderCode, Phase.renderIn, plug_invoke, code, expr, Op.instr, expression, List.append_assoc, values] using move
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
    exact Step.of_internal (framed_step (.label move (labelResults results labels).length []))
  | @armTrap bytes label labels =>
    have move := framed_step (scope := scopeFor results (label :: labels)) (outer := outer)
      (.pure (host := host) (mem.store bytes) active (.labelTrap label.type.signature.results.length []))
    simpa [render, Phase.renderCode, Phase.renderIn, labelResults, scopeFor, framed, values, List.append_assoc] using move
  | @armResult bytes stack label labels =>
    have move := framed_step (scope := scopeFor results (label :: labels)) (outer := outer)
      (.pure (host := host) (mem.store bytes) active (.labelDone label.type.signature.results.length [] stack))
    simpa [render, Phase.renderCode, Phase.renderIn, labelResults, scopeFor, framed, code, expr, expression,
      List.append_assoc] using move
  | labelTrap => exact .frame (.pure _ _ (.labelTrap results.length [])) results.length outer
  | @labelResult bytes stack =>
    have move := Step.frame (.pure (host := host) (mem.store bytes) active (.labelDone results.length [] stack))
      results.length outer
    simpa [render, Phase.renderCode, Phase.renderIn, scopeFor, labelResults, framed, code, expr, expression, result]
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
  exact sound ready edge

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs
