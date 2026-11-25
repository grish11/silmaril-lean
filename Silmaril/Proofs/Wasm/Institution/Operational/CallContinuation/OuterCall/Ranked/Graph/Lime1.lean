module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Context
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.NativeCommon
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Typing
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Native.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Native.Thms
import Silmaril.Wasm.Institution.Operational.Loops.Native.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Context.Thms
import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms

import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution
open Execution.Runtime (Frame FuncAddr Value)
open Computed

private abbrev native {H : Type} := Step (H := H) CallFrame.limeNoHost

private theorem code_expression (code : List Op) :
    expression (Op.emitList limeCodeSyntax code) = code.map limeAdmin.emit := by
  induction code with
  | nil => rfl
  | cons op rest ih =>
    change _ :: expression (Op.emitList limeCodeSyntax rest) = _ :: rest.map limeAdmin.emit
    rw [ih]
    cases op with
    | numeric op => cases op <;> rfl
    | set | tee | call | block | indexedBlock | indexedIf | loop | indexedLoop | if_ | br | brIf | brTable | return_ | unreachable => rfl

theorem expression_code (fn : Function) :
    expression fn.limeFunc.body = (Body.running fn.initial fn.code).render limeAdmin := by
  change expression (fn.initial.map Sequence.limeSource.value ++ Op.emitList limeCodeSyntax fn.code) =
    values fn.initial ++ fn.code.map limeAdmin.emit
  rw [show expression (fn.initial.map Sequence.limeSource.value ++ Op.emitList limeCodeSyntax fn.code) =
      expression (fn.initial.map Sequence.limeSource.value) ++ expression (Op.emitList limeCodeSyntax fn.code) from
    List.map_append .., code_expression]
  congr 1
  change (fn.initial.map Sequence.limeSource.value).map _ = _
  simp only [List.map_map, values]
  apply List.map_congr_left
  intro v _
  rcases v with ⟨t, bits⟩
  cases t <;> rfl

private def limeAt {H : Type} (s : Store H) (caller : Frame) (target : CallTarget) (n : Nat) (q : Phase) (kind : LabelKind := .exit) : Config H :=
  ⟨s, caller, q.renderAt limeAdmin target n kind⟩

private theorem attach_code (saved : List Value) (target : CallTarget) (rest : List Op) (q : Phase) :
    (Body.attach saved target rest q).render limeAdmin =
      values saved ++ q.render limeAdmin target ++ rest.map limeAdmin.emit :=
  render_attach values_append saved target rest q

private theorem lift_label {H : Type} {s : Store H} {caller parent parentNext : Frame} {n k : Nat} {cont : Wasm.Lime1.Expr}
    {before after : List Admin} (move : native ⟨s, parent, before⟩ ⟨s, parentNext, after⟩) :
    native ⟨s, caller, [.frame n parent [.label k cont before]]⟩
      ⟨s, caller, [.frame n parentNext [.label k cont after]]⟩ :=
  .frame (.label move k cont) n caller

private theorem set_sound {H : Type} {s : Store H} {decl : Declaration}
    {locals next saved : List Value} {v : Value} {idx : LocalIdx} {rest : List Op}
    (write : Locals.Edge ⟨locals, [.value v, .set idx]⟩ ⟨next, []⟩) :
    Step CallFrame.limeNoHost ⟨s, currentFrame decl locals, (Body.running (saved ++ [v]) (.set idx :: rest)).render limeAdmin⟩
      ⟨s, currentFrame decl next, (Body.running saved rest).render limeAdmin⟩ := by
  have move := Locals.lime_sound (host := CallFrame.limeNoHost) (s := s) (m := decl.module) write
  have lifted := Step.context move saved (rest.map limeAdmin.emit)
  rcases v with ⟨t, bits⟩
  cases t <;> simp [Locals.Codec.encode, Locals.limeCodec, Locals.legacyCodec,
    Locals.limeInstr, currentFrame, Body.render, limeAdmin, limeEmit, Op.emit, limeCodeSyntax,
    List.append_assoc, values] at lifted ⊢ <;> exact lifted

private theorem tee_sound {H : Type} {s : Store H} {decl : Declaration}
    {locals saved : List Value} {v : Value} {idx : LocalIdx} {rest : List Op}
    (write : Locals.Edge ⟨locals, [.value v, .tee idx]⟩ ⟨locals, [.value v, .value v, .set idx]⟩) :
    Step CallFrame.limeNoHost ⟨s, currentFrame decl locals, (Body.running (saved ++ [v]) (.tee idx :: rest)).render limeAdmin⟩
      ⟨s, currentFrame decl locals, (Body.running (saved ++ [v, v]) (.set idx :: rest)).render limeAdmin⟩ := by
  have move := Locals.lime_sound (host := CallFrame.limeNoHost) (s := s) (m := decl.module) write
  have lifted := Step.context move saved (rest.map limeAdmin.emit)
  rcases v with ⟨t, bits⟩
  cases t <;> simp [Locals.Codec.encode, Locals.limeCodec, Locals.legacyCodec,
    Locals.limeInstr, currentFrame, Body.render, limeAdmin, limeEmit, Op.emit, limeCodeSyntax,
    List.append_assoc, values] at lifted ⊢ <;> exact lifted

private theorem entry_iff {H : Type} {s : Store H} {caller : Frame} {fn : Function} {target : CallTarget}
    {saved args : List Value} {rest : List Admin} {dst : Config H}
    (declared : fn.declaration = target.declaration)
    (alloc : s.funcs[target.address.value]? = some (.wasm fn.declaration.type fn.declaration.module fn.limeFunc))
    (typed : args.map Value.type = fn.declaration.params) :
    native ⟨s, caller, values (saved ++ args) ++ .invoke target.address :: rest⟩ dst ↔
      dst = ⟨s, caller, values saved ++
        (Phase.label (fn.declaration.frame args).locals (.running fn.initial fn.code)).render limeAdmin target ++ rest⟩ := by
  have count : args.length = fn.declaration.type.params.length :=
    (List.length_map ..).symm.trans (congrArg List.length typed)
  have entry (out : Config H) :=
    CallFrame.lime_invoke_wasm_prefix_iff (caller := caller) (saved := saved) (dst := out) alloc count
  have entered : [.frame fn.declaration.type.results.length
      ⟨args ++ fn.limeFunc.locals.map Value.zero, fn.declaration.module⟩
      [.label fn.declaration.type.results.length [] (expression fn.limeFunc.body)]] =
      (Phase.label (fn.declaration.frame args).locals (.running fn.initial fn.code)).render limeAdmin target := by
    rw [expression_code, Phase.render, Phase.renderAt, ← declared]
    rfl
  constructor
  · intro move
    obtain ⟨mid, step, eq⟩ := CallContinuation.lime_invoke_strip_suffix move
    obtain rfl := (entry mid).mp step
    simpa only [← entered, List.append_assoc] using eq
  · rintro rfl
    have step := (entry _).mpr rfl
    simpa only [← entered, values, List.map_nil, List.nil_append, List.append_assoc, List.singleton_append] using
      Step.context step [] rest

private theorem running_stays {types : List Wasm.Lime1.FuncType} {n : Nat} {cont : Wasm.Lime1.Expr} {v : List Value} {op : Op}
    {rest : List Op} {out : List Admin}
    (notBranch : ∀ depth result, op ≠ .br depth result) (notReturn : op ≠ .return_)
    (pop : PureStep types [.label n cont ((Body.running v (op :: rest)).render limeAdmin)] out) : False := by
  change PureStep types [.label n cont (values v ++ limeAdmin.emit op :: rest.map limeAdmin.emit)] out at pop
  cases op with
  | numeric p =>
    cases p <;> exact Computed.lime_label_stays (head := limeAdmin.emit (.numeric _)) (by rfl)
      (by simp [limeAdmin, limeEmit, Prefix.emit, limeSyntax])
      (by simp [limeAdmin, limeEmit, Prefix.emit, limeSyntax])
      (by simp [limeAdmin, limeEmit, Prefix.emit, limeSyntax]) pop
  | set idx =>
    exact Computed.lime_label_stays (head := .source (.localSet idx)) rfl (by simp) (by simp) (by simp) pop
  | tee idx =>
    exact Computed.lime_label_stays (head := .source (.localTee idx)) rfl (by simp) (by simp) (by simp) pop
  | call t => exact Computed.lime_label_stays (head := .source (.call t.index)) rfl (by simp) (by simp) (by simp) pop
  | if_ result thenBody elseBody =>
    exact Computed.lime_label_stays (head := limeAdmin.emit (.if_ result thenBody elseBody)) rfl
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax])
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax])
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax]) pop
  | indexedIf index signature thenBody elseBody =>
    exact Computed.lime_label_stays (head := limeAdmin.emit (.indexedIf index signature thenBody elseBody)) rfl
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax])
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax])
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax]) pop
  | block result body =>
    exact Computed.lime_label_stays (head := limeAdmin.emit (.block result body)) rfl
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax])
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax])
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax]) pop
  | loop result body =>
    exact Computed.lime_label_stays (head := limeAdmin.emit (.loop result body)) rfl
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax])
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax])
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax]) pop
  | indexedLoop index signature body =>
    exact Computed.lime_label_stays (head := limeAdmin.emit (.indexedLoop index signature body)) rfl
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax])
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax])
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax]) pop
  | indexedBlock index signature body =>
    exact Computed.lime_label_stays (head := limeAdmin.emit (.indexedBlock index signature body)) rfl
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax])
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax])
      (by simp [limeAdmin, limeEmit, Op.emit, limeCodeSyntax]) pop
  | brTable depths fallback _ =>
    exact Computed.lime_label_stays (head := .source (.brTable depths fallback)) rfl
      (by simp) (by simp) (by simp) pop
  | brIf depth _ =>
    exact Computed.lime_label_stays (head := .source (.brIf depth)) rfl
      (by simp) (by simp) (by simp) pop
  | br depth result => exact notBranch depth result rfl
  | return_ => exact notReturn rfl
  | unreachable => exact Computed.lime_label_stays (head := .source .unreachable) rfl (by simp) (by simp) (by simp) pop

private theorem active_entered_iff {H : Type} {s : Store H} {program : Program} (n : Nat) {kind : LabelKind}
    {caller : Frame} {root target : CallTarget} {fn : Function}
    (found : program.lookup root.address = some fn) (used : target ∈ fn.targets)
    {locals saved : List Value} {rest : List Op} {child : Phase} (live : child.Active)
    {k : Nat} {f : Frame} {code : List Admin} (rendered : child.render limeAdmin target = [.frame k f code])
    (childStep : ∀ {dst}, native (limeConfig s (currentFrame root.declaration locals) target child) dst ↔
      ∃ out, program.FrameEdge target.address child out ∧ dst = limeConfig s (currentFrame root.declaration locals) target out)
    {dst : Config H} :
    native (limeAt s caller root n (.label locals (.active saved target child rest)) kind) dst ↔
      ∃ out, program.FrameEdgeAt root.address kind (.label locals (.active saved target child rest)) out ∧
        dst = limeAt s caller root n out kind := by
  have ctx : native (limeAt s caller root n (.label locals (.active saved target child rest)) kind) dst ↔
      ∃ mid, native (limeConfig s (currentFrame root.declaration locals) target child) mid ∧
        dst = ⟨mid.store, caller, [.frame n mid.frame
          [.label (kind.arity n) (kind.cont limeCodeSyntax) (values saved ++ mid.code ++ rest.map limeAdmin.emit)]]⟩ := by
    change native ⟨s, caller, [.frame n (currentFrame root.declaration locals)
        [.label (kind.arity n) (kind.cont limeCodeSyntax) (values saved ++ child.render limeAdmin target ++ rest.map limeAdmin.emit)]]⟩ dst ↔
      ∃ mid, native ⟨s, currentFrame root.declaration locals, child.render limeAdmin target⟩ mid ∧
        dst = ⟨mid.store, caller, [.frame n mid.frame
          [.label (kind.arity n) (kind.cont limeCodeSyntax) (values saved ++ mid.code ++ rest.map limeAdmin.emit)]]⟩
    rw [rendered, List.append_assoc, List.singleton_append]
    exact lime_entered_child_iff
  rw [ctx]
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨out, childEdge, rfl⟩ := childStep.mp move
    refine ⟨.label locals (Body.attach saved target rest out),
      (frame_active_iff found used live (kind := kind)).mpr ⟨out, childEdge, rfl⟩, ?_⟩
    change _ = (⟨s, caller, [.frame n _ [.label (kind.arity n) (kind.cont limeCodeSyntax) ((Body.attach saved target rest out).render limeAdmin)]]⟩ : Config H)
    rw [attach_code]
    rfl
  · rintro ⟨out, move, rfl⟩
    obtain ⟨childOut, childEdge, rfl⟩ := (frame_active_iff found used live (kind := kind)).mp move
    refine ⟨_, childStep.mpr ⟨childOut, childEdge, rfl⟩, ?_⟩
    change (⟨s, caller, [.frame n _ [.label (kind.arity n) (kind.cont limeCodeSyntax) ((Body.attach saved target rest childOut).render limeAdmin)]]⟩ : Config H) = _
    rw [attach_code]
    rfl

private theorem under_label_iff {H : Type} {s : Store H} {caller parent : Frame} {n k : Nat} {cont : Wasm.Lime1.Expr}
    {code : List Admin} {dst : Config H}
    (stays : ∀ {out}, PureStep parent.module.types [.label k cont code] out → False) :
    native ⟨s, caller, [.frame n parent [.label k cont code]]⟩ dst ↔
      ∃ mid : Config H, native ⟨s, parent, code⟩ mid ∧
        dst = ⟨mid.store, caller, [.frame n mid.frame [.label k cont mid.code]]⟩ := by
  constructor
  · intro move
    rcases Computed.lime_body_step_cases move with inside | ⟨_, pop, _⟩
    · exact inside
    · exact (stays pop).elim
  · rintro ⟨⟨_, _, _⟩, move, rfl⟩
    exact .frame (.label move k cont) n caller

private theorem pending_child_iff {H : Type} {s : Store H} {program : Program} (n : Nat) {kind : LabelKind}
    (allocated : program.LimeAllocated s) {caller : Frame} {root target : CallTarget} {fn callee : Function}
    (found : program.lookup root.address = some fn) (used : target ∈ fn.targets)
    (childFound : program.lookup target.address = some callee) (declared : callee.declaration = target.declaration)
    {locals saved operands : List Value} {rest : List Op} (typed : operands.map Value.type = callee.declaration.params)
    {dst : Config H} :
    native (limeAt s caller root n (.label locals (.active saved target (.invoke operands) rest)) kind) dst ↔
      ∃ out, program.FrameEdgeAt root.address kind (.label locals (.active saved target (.invoke operands) rest)) out ∧
        dst = limeAt s caller root n out kind := by
  have stays {out : List Admin} (pop : PureStep (currentFrame root.declaration locals).module.types
      [.label (kind.arity n) (kind.cont limeCodeSyntax)
        (values (saved ++ operands) ++ .invoke target.address :: rest.map limeAdmin.emit)] out) : False :=
    Computed.lime_label_stays (head := .invoke target.address) rfl (by simp) (by simp) (by simp) pop
  have ctx := under_label_iff (n := n) (s := s) (caller := caller) (dst := dst) stays
  have entry {mid : Config H} := entry_iff (caller := currentFrame root.declaration locals) (saved := saved)
    (rest := rest.map limeAdmin.emit) (dst := mid) declared (allocated _ _ childFound) typed
  have live : (Phase.invoke operands).Active := trivial
  have source : (Body.active saved target (.invoke operands) rest).render limeAdmin =
      values (saved ++ operands) ++ .invoke target.address :: rest.map limeAdmin.emit := by
    change values saved ++ (values operands ++ [.invoke target.address]) ++ rest.map limeAdmin.emit = _
    rw [values_append]
    simp only [List.append_assoc, List.singleton_append]
  change native ⟨s, caller, [.frame n _ [.label (kind.arity n) (kind.cont limeCodeSyntax) ((Body.active saved target (.invoke operands) rest).render limeAdmin)]]⟩ dst ↔ _
  rw [source, ctx]
  constructor
  · rintro ⟨mid, move, eq⟩
    obtain rfl := entry.mp move
    refine ⟨_, (frame_active_iff found used live (kind := kind)).mpr
      ⟨_, (frame_edge_iff childFound (kind := .exit)).mpr (.enter operands typed), rfl⟩, ?_⟩
    exact eq
  · rintro ⟨out, edge, rfl⟩
    obtain ⟨childOut, step, rfl⟩ := (frame_active_iff found used live (kind := kind)).mp edge
    cases (frame_edge_iff childFound (kind := .exit)).mp step with
    | enter _ _ => exact ⟨_, entry.mpr rfl, rfl⟩

private theorem trapped_not_final {n : Nat} {cont : Wasm.Lime1.Expr} {stack : List Value} {rest : List Op} {types : List Wasm.Lime1.FuncType}
    {out : List Admin} (pop : PureStep types [.label n cont ((Body.trapped stack rest).render limeAdmin)] out) :
    stack = [] ∧ rest = [] := by
  by_contra unfinished
  exact Computed.lime_label_stays (head := .trap) rfl (by simp) (by simp)
    (fun _ => by simpa using not_and_or.mp unfinished) pop

private theorem sequence_label_iff {H : Type} {s : Store H} {f : Frame} {n : Nat} {cont : Wasm.Lime1.Expr}
    {saved : List Value} {body rest : List Admin} {dst : Config H} :
    native ⟨s, f, values saved ++ .label n cont body :: rest⟩ dst ↔
      ∃ mid, native ⟨s, f, [.label n cont body]⟩ mid ∧
        dst = ⟨mid.store, mid.frame, values saved ++ mid.code ++ rest⟩ := by
  constructor
  · intro move
    rcases Blocks.Context.lime_label_cont_iff.mp move with ⟨mid, inside, rfl⟩ | ⟨out, pop, rfl⟩
    · exact ⟨_, .label inside n cont, by simp only [List.append_assoc, List.singleton_append]⟩
    · exact ⟨_, .pure s f pop, rfl⟩
  · rintro ⟨⟨_, _, _⟩, move, rfl⟩
    simpa only [List.append_assoc, List.singleton_append] using Step.context move saved rest

private def inFrame {H : Type} (outer : Frame) (n : Nat) (q : Config H) : Config H :=
  ⟨q.store, outer, [.frame n q.frame q.code]⟩

private theorem inFrame_injective {H : Type} (outer : Frame) (n : Nat) :
    Function.Injective (inFrame (H := H) outer n) := by
  intro a b eq
  cases a
  cases b
  simp_all [inFrame]

private theorem label_frame_iff {H : Type} {s : Store H} {outer inner : Frame}
    {n k : Nat} {cont : Wasm.Lime1.Expr} {body : List Admin} {dst : Config H} :
    native (inFrame outer n ⟨s, inner, [.label k cont body]⟩) dst ↔
      ∃ mid, native ⟨s, inner, [.label k cont body]⟩ mid ∧ dst = inFrame outer n mid := by
  constructor
  · intro move
    rcases Computed.lime_body_step_cases move with ⟨mid, inside, rfl⟩ | ⟨out, pop, rfl⟩
    · exact ⟨_, .label inside k cont, rfl⟩
    · exact ⟨_, .pure s inner pop, rfl⟩
  · rintro ⟨⟨_, _, _⟩, move, rfl⟩
    exact .frame move n outer

private theorem branch_step_iff {H : Type} {s : Store H} {program : Program}
    {caller : Frame} {target : CallTarget} {fn : Function}
    (found : program.lookup target.address = some fn) {fallthrough : List NumType} {enclosing : EnclosingLabels}
    {kind : LabelKind} {locals stack : List Value} {depth : LabelIdx} {result : List NumType} {rest : List Op}
    (typed : fn.WellTyped stack (.br depth result :: rest) fallthrough enclosing kind) {dst : Config H} :
    native (limeAt s caller target fallthrough.length (.label locals (.running stack (.br depth result :: rest))) kind) dst ↔
      ∃ out, program.FrameEdgeAt target.address kind (.label locals (.running stack (.br depth result :: rest))) out ∧
        dst = limeAt s caller target fallthrough.length out kind := by
  let n := fallthrough.length
  change native (inFrame caller n ⟨s, currentFrame target.declaration locals,
    [.label (kind.arity n) (kind.cont limeCodeSyntax) (values stack ++ .source (.br depth) :: rest.map limeAdmin.emit)]⟩) dst ↔ _
  rw [label_frame_iff]
  have rule {a b : Phase} := frame_edge_iff (a := a) (b := b) (kind := kind) found
  have invert {mid : Config H} := BranchExit.lime_label_br_cont_iff (host := CallFrame.limeNoHost) (s := s)
    (f := currentFrame target.declaration locals) (stack := stack)
    (n := kind.arity n) (cont := kind.cont limeCodeSyntax) (depth := depth) (rest := rest.map limeAdmin.emit) (dst := mid)
  have deliver (payload : List Value) (size : payload.length = kind.arity n) :
      limeAt s caller target n (kind.branchHere locals payload) kind =
        inFrame caller n ⟨s, currentFrame target.declaration locals, values payload ++ expression (kind.cont limeCodeSyntax)⟩ := by
    cases kind with
    | exit | indexed => simp [limeAt, Phase.renderAt, LabelKind.branchHere, LabelKind.cont,
        inFrame, Nested.resultCode, limeAdmin, expression]
    | loop result original =>
      have empty : payload = [] := List.eq_nil_of_length_eq_zero size
      subst payload
      rfl
    | indexedLoop => rfl
  constructor
  · rintro ⟨mid, move, rfl⟩
    rcases invert.mp move with ⟨extra, payload, split, size, here, rfl⟩ | ⟨outer, rfl⟩
    · subst stack
      have count := size
      obtain rfl : depth = ⟨0⟩ := Idx.toNat_injective here
      have arity := count.trans ((LabelKind.inputs_length kind fallthrough).symm.trans
        (congrArg List.length (branch_here_result (checked_branch typed).1)))
      exact ⟨_, rule.mpr (.branchHere locals extra payload result rest arity), (deliver payload count).symm⟩
    · exact ⟨_, rule.mpr (.branchOuter locals stack depth result rest outer), rfl⟩
  · rintro ⟨out, edge, rfl⟩
    cases rule.mp edge with
    | branchHere _ extra payload _ _ arity =>
      have size := arity.trans ((congrArg List.length (branch_here_result (checked_branch typed).1)).symm.trans
        (LabelKind.inputs_length kind fallthrough))
      exact ⟨_, invert.mpr (.inl ⟨extra, payload, rfl, size, rfl, rfl⟩), deliver payload size⟩
    | branchOuter _ _ _ _ _ outer =>
      exact ⟨_, invert.mpr (.inr ⟨outer, rfl⟩), rfl⟩

private theorem block_step_iff {H : Type} {s : Store H} {program : Program}
    {caller : Frame} {target : CallTarget} {fn : Function}
    (found : program.lookup target.address = some fn) {n : Nat} {kind innerKind : LabelKind} {locals saved : List Value} {result : Option NumType}
    {inner : Body} {rest : List Op}
    (compatible : ∀ r original, innerKind = .loop r original → r = result)
    (edgeView : ∀ {out}, program.FrameEdgeAt target.address kind (.label locals (inner.underLabel saved result rest innerKind)) out ↔
      ∃ next, program.FrameEdgeAt target.address innerKind (.label locals inner) next ∧
        out = next.afterBlock saved result rest innerKind)
    (inside : ∀ {dst}, native (limeAt s caller target (innerKind.results result).length (.label locals inner) innerKind) dst ↔
      ∃ next, program.FrameEdgeAt target.address innerKind (.label locals inner) next ∧
        dst = limeAt s caller target (innerKind.results result).length next innerKind)
    {dst : Config H} :
    native (limeAt s caller target n (.label locals (inner.underLabel saved result rest innerKind)) kind) dst ↔
      ∃ out, program.FrameEdgeAt target.address kind (.label locals (inner.underLabel saved result rest innerKind)) out ∧
        dst = limeAt s caller target n out kind := by
  let k := (innerKind.results result).length
  let code := values saved ++ (.label (innerKind.arity k) (innerKind.cont limeCodeSyntax) (inner.render limeAdmin) : Admin) :: rest.map limeAdmin.emit
  have stays {out} (pop : PureStep (currentFrame target.declaration locals).module.types [.label (kind.arity n) (kind.cont limeCodeSyntax) code] out) : False := by
    exact Computed.lime_label_stays (head := .label (innerKind.arity k) (innerKind.cont limeCodeSyntax) (inner.render limeAdmin)) rfl
      (by simp) (by simp) (by simp) pop
  have shape :
      limeAt s caller target n (.label locals (inner.underLabel saved result rest innerKind)) kind =
        ⟨s, caller, [.frame n (currentFrame target.declaration locals) [.label (kind.arity n) (kind.cont limeCodeSyntax) code]]⟩ := by
    rw [limeAt, Phase.renderAt, render_under_label limeAdmin saved result rest innerKind compatible]
    rfl
  rw [shape, under_label_iff stays]
  have render {next} (edge : program.FrameEdgeAt target.address innerKind (.label locals inner) next) :=
    render_block limeAdmin values_append rfl target n saved result rest kind innerKind compatible next
      (label_outcome ((frame_edge_iff found).mp edge) ⟨_, _, rfl⟩)
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨branch, step, rfl⟩ := (sequence_label_iff (saved := saved)).mp move
    have lifted : native (limeAt s caller target k (.label locals inner) innerKind) (inFrame caller k branch) := .frame step k caller
    obtain ⟨next, edge, eq⟩ := inside.mp lifted
    obtain ⟨ls, code, before, after⟩ := render edge
    have related : inFrame caller k (⟨s, (currentFrame target.declaration ls), code⟩ : Config H) =
        limeAt s caller target k next innerKind := by rw [limeAt, before]; rfl
    have same := inFrame_injective caller k (eq.trans related.symm)
    subst branch
    exact ⟨_, edgeView.mpr ⟨next, edge, rfl⟩, by rw [limeAt, after]; rfl⟩
  · rintro ⟨out, edge, rfl⟩
    obtain ⟨next, move, rfl⟩ := edgeView.mp edge
    have lifted := inside.mpr ⟨next, move, rfl⟩
    obtain ⟨branch, step, eq⟩ := label_frame_iff.mp lifted
    obtain ⟨ls, code, before, after⟩ := render move
    have related : limeAt s caller target k next innerKind =
        inFrame caller k (⟨s, (currentFrame target.declaration ls), code⟩ : Config H) := by
      rw [limeAt, before]; rfl
    have same := inFrame_injective caller k (eq.symm.trans related)
    subst branch
    refine ⟨_, (sequence_label_iff (saved := saved)).mpr ⟨_, step, rfl⟩, ?_⟩
    rw [limeAt, after]
    rfl

private theorem indexed_entry_iff {H : Type} {s : Store H} {decl : Declaration}
    {locals saved args : List Value} {index : TypeIdx} {signature : Wasm.V1.FuncType}
    {body : Wasm.Lime1.Expr} {rest : List Admin} {dst : Config H}
    (resolved : decl.module.types[index.toNat]? = some signature)
    (typed : args.map Value.type = signature.params) :
    native ⟨s, (currentFrame decl locals), values (saved ++ args) ++
      .source (.block (.typeIdx index) body) :: rest⟩ dst ↔
      dst = ⟨s, (currentFrame decl locals), values saved ++
        .label signature.results.length [] (values args ++ expression body) :: rest⟩ := by
  have lookup : blockType? decl.module.types (.typeIdx index) = some signature := resolved
  have arity : args.length = signature.params.length := by simpa using congrArg List.length typed
  rw [show native = Step CallFrame.limeNoHost from rfl, Computed.lime_block_step_iff]
  constructor
  · rintro ⟨kept, used, ft, split, found, size, rfl⟩
    change blockType? decl.module.types (.typeIdx index) = _ at found
    rw [lookup] at found
    cases found
    obtain ⟨rfl, rfl⟩ := List.append_inj' split (arity.trans size.symm)
    rfl
  · intro eq
    exact ⟨saved, args, _, rfl, lookup, arity, eq⟩

private theorem indexed_loop_entry_iff {H : Type} {s : Store H} {decl : Declaration}
    {locals saved args : List Value} {index : TypeIdx} {signature : Wasm.V1.FuncType}
    {body : Wasm.Lime1.Expr} {rest : List Admin} {dst : Config H}
    (resolved : decl.module.types[index.toNat]? = some signature)
    (typed : args.map Value.type = signature.params) :
    native ⟨s, (currentFrame decl locals), values (saved ++ args) ++
      .source (.loop (.typeIdx index) body) :: rest⟩ dst ↔
      dst = ⟨s, (currentFrame decl locals), values saved ++
        .label signature.params.length [.loop (.typeIdx index) body] (values args ++ expression body) :: rest⟩ := by
  have lookup : blockType? decl.module.types (.typeIdx index) = some signature := resolved
  have arity : args.length = signature.params.length := by simpa using congrArg List.length typed
  rw [show native = Step CallFrame.limeNoHost from rfl, Computed.lime_loop_step_iff]
  constructor
  · rintro ⟨kept, used, ft, split, found, size, rfl⟩
    change blockType? decl.module.types (.typeIdx index) = _ at found
    rw [lookup] at found
    cases found
    obtain ⟨rfl, rfl⟩ := List.append_inj' split (arity.trans size.symm)
    rfl
  · intro eq
    exact ⟨saved, args, _, rfl, lookup, arity, eq⟩

private theorem region_step_iff {H : Type} {s : Store H} {program : Program} (checked : program.checkDirect = true)
    (allocated : program.LimeAllocated s) {caller : Frame} {target : CallTarget} {fn : Function}
    (rootFound : program.lookup target.address = some fn)
    (rootDeclared : fn.declaration = target.declaration)
    {bound : Nat}
    (descend : ∀ child, ∀ {parent callee q dst}, sizeOf q < bound →
      Root program parent child callee → Admitted program callee q →
      (native (limeConfig s parent child q) dst ↔
        ∃ out, program.FrameEdge child.address q out ∧ dst = limeConfig s parent child out))
    (size : Nat) : ∀ {body locals fallthrough enclosing kind dst}, sizeOf body = size → size < bound →
      AdmittedAt program fn fallthrough enclosing (.label locals body) kind →
      (native (limeAt s caller target fallthrough.length (.label locals body) kind) dst ↔
        ∃ out, program.FrameEdgeAt target.address kind (.label locals body) out ∧
          dst = limeAt s caller target fallthrough.length out kind) := by
  induction size using Nat.strong_induction_on with
  | ind size ih =>
    intro body locals fallthrough enclosing kind dst sizeEq within ready
    let n := fallthrough.length
    let k := kind.arity n
    let cont := kind.cont limeCodeSyntax
    have rule {a b : Phase} := frame_edge_iff (a := a) (b := b) (kind := kind) rootFound
    cases ready with
    | @running _ _ _ _ locals stack rest typed codeTyped =>
      cases rest with
      | nil =>
        constructor
        · intro move
          rcases Computed.lime_body_step_cases move with ⟨_, inside, _⟩ | ⟨_, pop, eq⟩
          · exact (Nested.lime_result_stuck (r := .values stack) (by simpa only [Body.render, limeAdmin,
              List.map_nil, List.append_nil, Nested.resultCode] using inside)).elim
          · exact ⟨_, rule.mpr (.leaveValues locals stack), eq.trans (by
              have leave := Nested.lime_label_result (r := .values stack)
                (by simpa only [Body.render, limeAdmin, List.map_nil, List.append_nil, Nested.resultCode] using pop)
              rw [leave]
              rfl)⟩
        · rintro ⟨out, move, rfl⟩
          cases rule.mp move with
          | leaveValues =>
            simpa only [limeAt, Phase.renderAt, Body.render, limeAdmin, List.map_nil, List.append_nil, Nested.resultCode] using
              Step.frame (Step.pure (host := CallFrame.limeNoHost) s (currentFrame target.declaration locals)
                (.labelDone k cont stack)) n caller
      | cons op rest =>
        by_cases isBranch : ∃ depth result, op = .br depth result
        · obtain ⟨depth, result, rfl⟩ := isBranch
          exact branch_step_iff rootFound codeTyped
        have notBranch depth result (eq : op = .br depth result) : False := isBranch ⟨_, _, eq⟩
        by_cases isReturn : op = .return_
        case pos =>
          subst op
          constructor
          · intro move
            rcases Computed.lime_body_step_cases move with ⟨_, inside, _⟩ | ⟨_, pop, eq⟩
            · exact (CallFrame.lime_return_stuck (stack := stack) (tail := rest.map limeAdmin.emit) inside).elim
            · exact ⟨_, rule.mpr (.returnLabel locals stack rest),
                eq.trans (by rw [CallFrame.lime_return_label_result pop]; rfl)⟩
          · rintro ⟨out, move, rfl⟩
            cases rule.mp move with
            | returnLabel =>
              simpa only [limeAt, Phase.renderAt, Body.render, limeAdmin, List.map_cons,
                limeEmit, Op.emit, limeCodeSyntax, List.append_assoc, List.singleton_append, n, k, cont] using
                Step.frame (Step.pure (host := CallFrame.limeNoHost) s (currentFrame target.declaration locals)
                  (.labelReturn k cont stack (rest.map limeAdmin.emit)))
                  n caller
        have stays {out : List Admin} := running_stays (types := (currentFrame target.declaration locals).module.types)
          (n := k) (cont := cont) (v := stack) (op := op) (rest := rest) notBranch isReturn (out := out)
        constructor
        · intro move
          obtain ⟨mid, inner, eq⟩ := (under_label_iff stays).mp move
          cases op with
          | br depth result => exact (notBranch depth result rfl).elim
          | return_ => exact (isReturn rfl).elim
          | numeric op =>
            have reduction := (Prefix.lime_step_iff (op := op) (tail := rest.map limeAdmin.emit)).mp inner
            obtain ⟨answer, reduce, rfl⟩ := reduction
            exact ⟨_, rule.mpr (.numeric reduce), eq.trans (by cases answer <;> rfl)⟩
          | set idx =>
            obtain ⟨saved, value, next, rfl, write, rfl⟩ := Computed.lime_set_read (f := currentFrame target.declaration locals) inner
            exact ⟨_, rule.mpr (.localSet write), eq⟩
          | tee idx =>
            obtain ⟨saved, value, rfl, write, rfl⟩ := Computed.lime_tee_read (f := currentFrame target.declaration locals) inner
            exact ⟨_, rule.mpr (.localTee write), eq⟩
          | call child =>
            obtain ⟨saved, operands, rfl, used, count⟩ := split_call codeTyped
            obtain ⟨_, _, _, resolves⟩ := linked_direct_target checked rootFound used
            have h : (currentFrame target.declaration locals).module.funcs[child.index.toNat]? = some child.address := by
              simpa only [currentFrame, ← rootDeclared] using resolves
            obtain rfl := (Computed.lime_direct_call_iff (stack := saved ++ operands)
              (tail := rest.map limeAdmin.emit) h).mp inner
            exact ⟨_, rule.mpr (.dispatch locals saved operands child rest used count), eq.trans (by
              simp only [limeAt, Phase.renderAt, Body.render, limeAdmin, values_append,
                List.append_assoc, List.singleton_append]
              rfl)⟩
          | brTable depths fallback result =>
            obtain ⟨saved, selector, rfl⟩ := Function.split_br_table codeTyped
            have select := (Computed.lime_br_table_iff (s := s) (f := currentFrame target.declaration locals)
              (saved := saved) (selector := selector) (depths := depths) (fallback := fallback)
              (rest := rest.map limeAdmin.emit)).mp inner
            subst mid
            exact ⟨_, rule.mpr (.branchTable locals saved selector depths fallback result rest), eq⟩
          | brIf depth result =>
            obtain ⟨saved, condition, rfl⟩ := Function.split_br_if codeTyped
            have select := (Computed.lime_br_if_iff (s := s) (f := currentFrame target.declaration locals)
              (saved := saved) (condition := condition) (depth := depth) (rest := rest.map limeAdmin.emit)).mp inner
            subst mid
            exact ⟨_, rule.mpr (.branchIf locals saved condition depth result rest), eq.trans (by
              simp only [limeAt, Phase.renderAt, Body.render, Op.map_br_if, limeAdmin, limeEmit,
                Op.emit, limeCodeSyntax, List.append_assoc]
              rfl)⟩
          | if_ result thenBody elseBody =>
            obtain ⟨saved, condition, rfl⟩ := Function.split_if codeTyped
            have select := (Computed.lime_if_iff (s := s) (f := currentFrame target.declaration locals)
              (bt := Blocks.limeType result) (saved := saved) (condition := condition)
              (thenBody := Op.emitList limeCodeSyntax thenBody)
              (elseBody := Op.emitList limeCodeSyntax elseBody) (rest := rest.map limeAdmin.emit)).mp inner
            subst mid
            refine ⟨_, rule.mpr (.ifSelect locals saved condition result thenBody elseBody rest), ?_⟩
            exact eq.trans (by
              simp only [limeAt, Phase.renderAt, Body.render, limeAdmin, limeEmit, Op.emit,
                limeCodeSyntax, Function.comp_def, Op.emitList_selected, List.map_cons]
              rfl)
          | indexedIf index signature thenBody elseBody =>
            obtain ⟨saved, condition, rfl⟩ := Function.split_indexed_if codeTyped
            have select := (Computed.lime_if_iff (s := s) (f := currentFrame target.declaration locals)
              (bt := .typeIdx index) (saved := saved) (condition := condition)
              (thenBody := Op.emitList limeCodeSyntax thenBody)
              (elseBody := Op.emitList limeCodeSyntax elseBody) (rest := rest.map limeAdmin.emit)).mp inner
            subst mid
            refine ⟨_, rule.mpr (.indexedIfSelect locals saved condition index signature thenBody elseBody rest), ?_⟩
            exact eq.trans (by
              simp only [limeAt, Phase.renderAt, Body.render, limeAdmin, limeEmit, Op.emit,
                limeCodeSyntax, Function.comp_def, Op.emitList_selected, List.map_cons]
              rfl)
          | block result body =>
            have enter := (Computed.lime_block_iff (result := result)
              (body := Op.emitList limeCodeSyntax body) (stack := stack) (rest := rest.map limeAdmin.emit)).mp inner
            rw [code_expression] at enter
            exact ⟨_, rule.mpr (.blockEnter locals stack result body rest), eq.trans
              (congrArg (fun x : Config H =>
                (⟨x.store, caller, [.frame n x.frame [.label k cont x.code]]⟩ : Config H)) enter)⟩
          | indexedBlock index signature body =>
            obtain ⟨saved, args, rfl, typed, resolved⟩ := split_indexed_block codeTyped
            have inModule : target.declaration.module.types[index.toNat]? = some signature := by
              simpa only [← rootDeclared] using resolved
            have enter := (indexed_entry_iff (s := s) (locals := locals) (saved := saved) (args := args)
              (body := Op.emitList limeCodeSyntax body) (rest := rest.map limeAdmin.emit)
              inModule typed).mp inner
            rw [code_expression] at enter
            exact ⟨_, rule.mpr (.indexedBlockEnter locals saved args index signature body rest resolved typed),
              eq.trans (congrArg (fun x : Config H =>
                (⟨x.store, caller, [.frame n x.frame [.label k cont x.code]]⟩ : Config H)) enter)⟩
          | indexedLoop index signature body =>
            obtain ⟨saved, args, rfl, typed, resolved⟩ := split_indexed_loop codeTyped
            have inModule : target.declaration.module.types[index.toNat]? = some signature := by
              simpa only [← rootDeclared] using resolved
            have enter := (indexed_loop_entry_iff (s := s) (locals := locals) (saved := saved) (args := args)
              (body := Op.emitList limeCodeSyntax body) (rest := rest.map limeAdmin.emit)
              inModule typed).mp inner
            rw [code_expression] at enter
            exact ⟨_, rule.mpr (.indexedLoopEnter locals saved args index signature body rest resolved typed),
              eq.trans (congrArg (fun x : Config H =>
                (⟨x.store, caller, [.frame n x.frame [.label k cont x.code]]⟩ : Config H)) enter)⟩
          | loop result body =>
            have enter := (Loops.lime_entry_iff (result := result)
              (body := Op.emitList limeCodeSyntax body) (saved := stack) (rest := rest.map limeAdmin.emit)).mp inner
            rw [code_expression] at enter
            exact ⟨_, rule.mpr (.loopEnter locals stack result body rest), eq.trans
              (congrArg (fun x : Config H =>
                (⟨x.store, caller, [.frame n x.frame [.label k cont x.code]]⟩ : Config H)) enter)⟩
          | unreachable =>
            obtain rfl := Computed.lime_unreachable_iff.mp inner
            exact ⟨_, rule.mpr (.unreachable locals stack rest), eq⟩
        · rintro ⟨out, move, rfl⟩
          cases rule.mp move with
          | branchHere | branchOuter => exact (isBranch ⟨_, _, rfl⟩).elim
          | returnLabel => exact (isReturn rfl).elim
          | @numeric _ locals stack op rest answer reduce =>
            apply lift_label
            exact (Prefix.lime_step_iff (s := s) (f := currentFrame target.declaration locals) (stack := stack)
              (op := op) (tail := rest.map limeAdmin.emit)).mpr ⟨answer, reduce, by cases answer <;> rfl⟩
          | @localSet _ locals next saved i value rest write =>
            exact lift_label (set_sound write)
          | @localTee _ locals saved i value rest write =>
            exact lift_label (tee_sound write)
          | dispatch _ saved operands child rest used count =>
            obtain ⟨_, _, _, resolves⟩ := linked_direct_target checked rootFound used
            have h : (currentFrame target.declaration locals).module.funcs[child.index.toNat]? = some child.address := by
              simpa only [currentFrame, ← rootDeclared] using resolves
            apply lift_label
            simpa only [Body.render, Phase.render, Phase.renderAt, limeAdmin, limeEmit, Op.emit, limeCodeSyntax, Sequence.limeSource, Function.comp_def, values_append, List.map_cons, List.append_assoc, List.singleton_append] using
              (Computed.lime_direct_call_iff (stack := saved ++ operands) (tail := rest.map limeAdmin.emit) h).mpr rfl
          | branchTable _ saved selector depths fallback result rest =>
            apply lift_label
            have select := (Computed.lime_br_table_iff (s := s) (f := currentFrame target.declaration locals)
              (saved := saved) (selector := selector) (depths := depths) (fallback := fallback)
              (rest := rest.map limeAdmin.emit)).mpr rfl
            simpa only [native, Body.render, limeAdmin, limeEmit, Op.emit, limeCodeSyntax,
              List.map_append, List.map_cons, List.map_nil] using select
          | branchIf _ saved condition depth result rest =>
            apply lift_label
            have select := (Computed.lime_br_if_iff (s := s) (f := currentFrame target.declaration locals)
              (saved := saved) (condition := condition) (depth := depth) (rest := rest.map limeAdmin.emit)).mpr rfl
            simpa only [native, Body.render, Op.map_br_if, limeAdmin, limeEmit, Op.emit, limeCodeSyntax,
              List.append_assoc, List.map_append, List.map_cons, List.map_nil] using select
          | @ifSelect _ locals saved condition result thenBody elseBody rest =>
            apply lift_label
            have select := (Computed.lime_if_iff (s := s) (f := currentFrame target.declaration locals)
              (bt := Blocks.limeType result) (saved := saved)
              (condition := condition)
              (thenBody := Op.emitList limeCodeSyntax thenBody)
              (elseBody := Op.emitList limeCodeSyntax elseBody) (rest := rest.map limeAdmin.emit)).mpr rfl
            simpa only [Body.render, limeAdmin, limeEmit, Op.emit, limeCodeSyntax, Function.comp_def,
              Op.emitList_selected, List.map_cons, List.map_append, List.map_nil] using select
          | @indexedIfSelect _ locals saved condition index _ thenBody elseBody rest =>
            apply lift_label
            have select := (Computed.lime_if_iff (s := s) (f := currentFrame target.declaration locals)
              (bt := .typeIdx index) (saved := saved)
              (condition := condition)
              (thenBody := Op.emitList limeCodeSyntax thenBody)
              (elseBody := Op.emitList limeCodeSyntax elseBody) (rest := rest.map limeAdmin.emit)).mpr rfl
            simpa only [Body.render, limeAdmin, limeEmit, Op.emit, limeCodeSyntax, Function.comp_def,
              Op.emitList_selected, List.map_cons, List.map_append, List.map_nil] using select
          | blockEnter =>
            rename_i result body
            apply lift_label
            exact (Computed.lime_block_iff (result := result) (body := Op.emitList limeCodeSyntax body)
              (stack := stack) (rest := rest.map limeAdmin.emit)).mpr (by rw [code_expression]; rfl)
          | indexedBlockEnter locals saved args index signature body rest resolved typed =>
            have inModule : target.declaration.module.types[index.toNat]? = some signature := by
              simpa only [← rootDeclared] using resolved
            apply lift_label
            exact (indexed_entry_iff (saved := saved) (body := Op.emitList limeCodeSyntax body)
              (rest := rest.map limeAdmin.emit) inModule typed).mpr (by rw [code_expression]; rfl)
          | indexedLoopEnter locals saved args index signature body rest resolved typed =>
            have inModule : target.declaration.module.types[index.toNat]? = some signature := by
              simpa only [← rootDeclared] using resolved
            apply lift_label
            exact (indexed_loop_entry_iff (saved := saved) (body := Op.emitList limeCodeSyntax body)
              (rest := rest.map limeAdmin.emit) inModule typed).mpr (by rw [code_expression]; rfl)
          | loopEnter =>
            rename_i result body
            apply lift_label
            exact (Loops.lime_entry_iff (result := result) (body := Op.emitList limeCodeSyntax body)
              (saved := stack) (rest := rest.map limeAdmin.emit)).mpr (by rw [code_expression]; rfl)
          | unreachable =>
            exact lift_label (Computed.lime_unreachable_iff.mpr rfl)
    | @active _ _ _ _ locals saved child q rest callee typed used childFound declared live childReady resume =>
      obtain ⟨_, _, _, resolves⟩ := linked_direct_target checked rootFound used
      have childResolves : child.Resolves (currentFrame target.declaration locals) := by
        simpa only [CallTarget.Resolves, currentFrame, ← rootDeclared] using resolves
      have smaller : sizeOf q < size := by
        rw [← sizeEq]
        simp only [Body.active.sizeOf_spec]
        omega
      have childStep {next : Config H} := descend child (smaller.trans within)
        (dst := next) ⟨childFound, declared, childResolves⟩ childReady
      cases q with
      | call | branching | restart | indexedRestart | done => cases live
      | invoke operands =>
        cases childReady with
        | invoke localsTyped => exact pending_child_iff n allocated rootFound used childFound declared localsTyped
      | label | returning | exit => exact active_entered_iff n rootFound used live rfl childStep
    | @trapped _ _ _ _ locals saved rest typed =>
      constructor
      · intro move
        rcases Computed.lime_body_step_cases move with ⟨mid, inside, eq⟩ | ⟨_, pop, eq⟩
        · obtain ⟨kept, remaining, cut, rfl⟩ := (Prefix.lime_discard_iff limeAdmin.emit).mp inside
          exact ⟨_, rule.mpr (.discard cut), eq⟩
        · obtain ⟨rfl, rfl⟩ := trapped_not_final pop
          exact ⟨_, rule.mpr (.leaveTrap locals), eq.trans (by rw [Nested.lime_label_result (r := .trap) pop]; rfl)⟩
      · rintro ⟨out, move, rfl⟩
        cases rule.mp move with
        | discard cut => exact lift_label ((Prefix.lime_discard_iff limeAdmin.emit).mpr ⟨_, _, cut, rfl⟩)
        | leaveTrap => exact .frame (.pure s _ (.labelTrap k cont)) n caller
    | @block _ _ _ _ locals saved result inside rest innerTyped resume =>
      have smaller : sizeOf inside < size := by rw [← sizeEq]; simp [Body.block.sizeOf_spec]; omega
      exact block_step_iff rootFound (n := n) (innerKind := .exit)
        (by simp) (block_iff rootFound) (fun {dst} =>
          ih (sizeOf inside) smaller (dst := dst) rfl (smaller.trans within) innerTyped)
    | @indexedBlock _ _ _ _ locals saved signature inside rest innerTyped resume =>
      have smaller : sizeOf inside < size := by rw [← sizeEq]; simp [Body.indexedBlock.sizeOf_spec]; omega
      exact block_step_iff rootFound (n := n) (result := none) (innerKind := .indexed signature)
        (by simp) (indexed_block_iff rootFound) (fun {dst} =>
          ih (sizeOf inside) smaller (dst := dst) rfl (smaller.trans within) innerTyped)
    | @loop _ _ _ _ locals saved result original inside rest innerTyped _ resume =>
      have smaller : sizeOf inside < size := by rw [← sizeEq]; simp [Body.loop.sizeOf_spec]; omega
      exact block_step_iff rootFound (n := n) (innerKind := .loop result original)
        (fun _ _ eq => (LabelKind.loop.inj eq).1.symm) (loop_iff rootFound) (fun {dst} =>
          ih (sizeOf inside) smaller (dst := dst) rfl (smaller.trans within) innerTyped)
    | @indexedLoop _ _ _ _ locals saved index signature original inside rest innerTyped _ _ resume =>
      have smaller : sizeOf inside < size := by rw [← sizeEq]; simp [Body.indexedLoop.sizeOf_spec]; omega
      exact block_step_iff rootFound (n := n) (innerKind := .indexedLoop index signature original)
        (fun _ _ eq => by cases eq) (indexed_loop_iff rootFound) (fun {dst} =>
          ih (sizeOf inside) smaller (dst := dst) rfl (smaller.trans within) innerTyped)

theorem resolved_frame_step_iff {H : Type} {s : Store H} {program : Program} (checked : program.checkDirect = true)
    (allocated : program.LimeAllocated s) (size : Nat) :
    ∀ {caller target fn a dst}, sizeOf a = size →
      (program.lookup target.address = some fn) → (fn.declaration = target.declaration) →
      (∀ args, a = .call args → target.Resolves caller) → Admitted program fn a →
      (Step CallFrame.limeNoHost (limeConfig s caller target a) dst ↔
        ∃ out, program.FrameEdge target.address a out ∧ dst = limeConfig s caller target out) := by
  induction size using Nat.strong_induction_on with
  | ind size ih =>
    intro caller target fn a dst sizeEq found declared resolves ready
    have rule {a b : Phase} := frame_edge_iff (a := a) (b := b) (kind := .exit) found
    have descend child {parent callee q dst} (smaller : sizeOf q < size)
        (childRoot : Root program parent child callee) (childReady : Admitted program callee q) :=
      ih (sizeOf q) smaller (dst := dst) rfl childRoot.found childRoot.declared (fun _ _ => childRoot.resolves) childReady
    have region {locals body} (eq : sizeOf (Phase.label locals body) = size)
        (ok : Admitted program fn (.label locals body)) :
        native (limeConfig s caller target (.label locals body)) dst ↔
          ∃ out, program.FrameEdge target.address (.label locals body) out ∧ dst = limeConfig s caller target out := by
      have bound : sizeOf body < size := by
        simp only [Phase.label.sizeOf_spec] at eq
        omega
      simpa only [limeConfig, limeAt, Phase.render, declared] using
        region_step_iff checked allocated found declared descend (sizeOf body) (dst := dst) rfl bound ok
    cases ready with
    | @call _ args typed =>
      have callLookup := resolves args rfl
      have move := Computed.lime_direct_call_iff (s := s) (stack := args) (tail := []) (dst := dst) callLookup
      constructor
      · intro h
        exact ⟨_, rule.mpr (.resolve args), move.mp h⟩
      · rintro ⟨out, h, rfl⟩
        cases rule.mp h with
        | resolve => exact (Computed.lime_direct_call_iff callLookup).mpr rfl
    | @invoke _ args typed =>
      have move := entry_iff (caller := caller) (saved := []) (rest := []) (dst := dst) declared
        (allocated _ _ found) typed
      constructor
      · intro step
        refine ⟨_, rule.mpr (.enter args typed), ?_⟩
        exact (move.mp step).trans (by simp [limeConfig, values])
      · rintro ⟨out, step, rfl⟩
        cases rule.mp step with
        | enter =>
          change native ⟨s, caller, values args ++ [.invoke target.address]⟩
            ⟨s, caller, (Phase.label (fn.declaration.frame args).locals (.running fn.initial fn.code)).render limeAdmin target⟩
          simpa only [values, List.map_nil, List.nil_append, List.append_nil] using
            (entry_iff (caller := caller) (saved := []) (rest := []) declared (allocated _ _ found) typed).mpr rfl
    | running typed code => exact region sizeEq (.running typed code)
    | active typed used found declared live ready resume => exact region sizeEq (.active typed used found declared live ready resume)
    | block inside resume => exact region sizeEq (.block inside resume)
    | indexedBlock inside resume => exact region sizeEq (.indexedBlock inside resume)
    | indexedLoop inside resolved original resume => exact region sizeEq (.indexedLoop inside resolved original resume)
    | loop inside original resume => exact region sizeEq (.loop inside original resume)
    | trapped typed => exact region sizeEq (.trapped typed)
    | @returning _ _ _ _ locals stack typed returnTyped =>
      constructor
      · intro move
        obtain ⟨extra, results, rfl, arity⟩ := split_return returnTyped
        have count := arity.trans (congrArg (fun d => d.results.length) declared)
        exact ⟨_, rule.mpr (.returnFrame locals extra results arity),
          (CallFrame.lime_return_frame_iff count).mp move⟩
      · rintro ⟨out, move, rfl⟩
        cases rule.mp move with
        | returnFrame locals dropped returned arity =>
          exact (CallFrame.lime_return_frame_iff
            (arity.trans (congrArg (fun d => d.results.length) declared))).mpr rfl
    | @exit _ _ _ _ locals result typed outTyped =>
      constructor
      · intro move
        exact ⟨_, rule.mpr (.leaveFrame locals result outTyped), Nested.lime_frame_result move⟩
      · rintro ⟨out, move, rfl⟩
        cases rule.mp move with
        | leaveFrame =>
          cases result with
          | trap => exact .pure s caller (.frameTrap _ _)
          | values xs =>
            exact .pure s caller (.frameDone _ _ xs ((result_length outTyped).trans
              (congrArg (fun d => d.results.length) declared)))
    | branching _ target _ => simp at target
    | @done _ _ _ _ result typed =>
      constructor
      · intro step
        exact (Nested.lime_result_stuck step).elim
      · rintro ⟨_, step, _⟩
        cases rule.mp step

theorem frame_step_iff {H : Type} {s : Store H} {program : Program} (checked : program.checkDirect = true)
    (allocated : program.LimeAllocated s) (size : Nat) :
    ∀ {caller target fn a dst}, sizeOf a = size →
      Root program caller target fn → Admitted program fn a →
      (Step CallFrame.limeNoHost (limeConfig s caller target a) dst ↔
        ∃ out, program.FrameEdge target.address a out ∧ dst = limeConfig s caller target out) :=
  fun sizeEq root => resolved_frame_step_iff checked allocated size sizeEq root.found root.declared
    (fun _ _ => root.resolves)

theorem step_iff {H : Type} {s : Store H} {program : Program} (checked : program.check = true)
    (allocated : program.LimeAllocated s)
    {caller : Frame} {target : CallTarget} {fn : Function} {a : Phase} {dst : Config H}
    (root : Root program caller target fn) (ready : Admitted program fn a) :
    Step CallFrame.limeNoHost (limeConfig s caller target a) dst ↔
      ∃ out, program.Edge checked target.address a out ∧ dst = limeConfig s caller target out :=
  (frame_step_iff (check_direct_of_ranked checked) allocated _ rfl root ready).trans (by
    simp only [Program.FrameEdge, Program.Edge, frame_edge_iff_ranked checked])

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs.Lime1
