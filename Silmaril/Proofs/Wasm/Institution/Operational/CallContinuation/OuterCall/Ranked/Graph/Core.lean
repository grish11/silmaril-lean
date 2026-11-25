module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
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
import Silmaril.Wasm.Execution.Core.Sim.Context
import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms
import Silmaril.Wasm.Execution.Core.Inversion.Thms

import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs.Core

open Execution.Core
open Execution
open Execution.Runtime (FuncAddr Value)
open Computed
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

private abbrev native {H : Type} (P : Profile) := Step (H := H) P noHost

private theorem code_expression (code : List Op) :
    expression (Op.emitList coreCodeSyntax code) = code.map coreAdmin.emit := by
  induction code with
  | nil => rfl
  | cons op rest ih =>
    change _ :: expression (Op.emitList coreCodeSyntax rest) = _ :: rest.map coreAdmin.emit
    rw [ih]
    cases op with
    | numeric op => cases op <;> rfl
    | set | tee | call | block | indexedBlock | indexedIf | loop | indexedLoop | if_ | br | brIf | brTable | return_ | unreachable => rfl

theorem expression_code (fn : Function) :
    expression fn.coreFunc.body = (Body.running fn.initial fn.code).render coreAdmin := by
  change expression (fn.initial.map Sequence.coreSource.value ++ Op.emitList coreCodeSyntax fn.code) =
    coreValues fn.initial ++ fn.code.map coreAdmin.emit
  rw [show expression (fn.initial.map Sequence.coreSource.value ++ Op.emitList coreCodeSyntax fn.code) =
      expression (fn.initial.map Sequence.coreSource.value) ++ expression (Op.emitList coreCodeSyntax fn.code) from
    List.map_append .., code_expression]
  congr 1
  change (fn.initial.map Sequence.coreSource.value).map _ = _
  simp only [List.map_map, coreValues, vals]
  apply List.map_congr_left
  intro v _
  rcases v with ⟨t, bits⟩
  cases t <;> rfl

private def coreAt {H : Type} (s : Store H) (caller : Runtime.Frame) (target : CallTarget) (n : Nat) (q : Phase) (kind : LabelKind := .exit) : Config H :=
  ⟨s, caller.toCore, q.renderAt coreAdmin target n kind⟩

private theorem values_append (xs ys : List Value) :
    coreValues (xs ++ ys) = coreValues xs ++ coreValues ys := by
  simp only [coreValues, List.map_append, vals_append]

private theorem attach_code (saved : List Value) (target : CallTarget) (rest : List Op) (q : Phase) :
    (Body.attach saved target rest q).render coreAdmin =
      coreValues saved ++ q.render coreAdmin target ++ rest.map coreAdmin.emit :=
  render_attach values_append saved target rest q

private theorem lift_label {H : Type} {P : Profile} {s : Store H} {caller : Runtime.Frame}
    {parent parentNext : Frame} {n k : Nat} {cont : List Instr} {before after : List Admin}
    (move : native P ⟨s, parent, before⟩ ⟨s, parentNext, after⟩) :
    native P ⟨s, caller.toCore, [.frame n parent [.label k cont before]]⟩
      ⟨s, caller.toCore, [.frame n parentNext [.label k cont after]]⟩ :=
  .ctxtFrame (.ctxtLabel move)

private theorem set_sound {H : Type} {P : Profile} {s : Store H} {decl : Declaration}
    {locals next saved : List Value} {v : Value} {idx : LocalIdx} {rest : List Op}
    (write : Locals.Edge ⟨locals, [.value v, .set idx]⟩ ⟨next, []⟩) :
    native P ⟨s, (currentFrame decl locals).toCore, (Body.running (saved ++ [v]) (.set idx :: rest)).render coreAdmin⟩
      ⟨s, (currentFrame decl next).toCore, (Body.running saved rest).render coreAdmin⟩ := by
  have move := Locals.core_sound (P := P) (s := s) (m := decl.module.toCore) write
  have lifted := Wasm.SingleThreaded.Det.lift_instrs (saved.map Value.toCore) (rest.map coreAdmin.emit) _ _ move
  rcases v with ⟨t, bits⟩
  cases t <;> simp [Locals.coreConfig, Locals.Codec.encode, Locals.coreCodec, Locals.coreInstr,
    Execution.Runtime.Frame.toCore, currentFrame, Body.render, coreAdmin, coreEmit, Op.emit, coreCodeSyntax,
    coreValues, vals, List.map_append, List.append_assoc, Function.comp_def] at lifted ⊢ <;> exact lifted

private theorem tee_sound {H : Type} {P : Profile} {s : Store H} {decl : Declaration}
    {locals saved : List Value} {v : Value} {idx : LocalIdx} {rest : List Op}
    (write : Locals.Edge ⟨locals, [.value v, .tee idx]⟩ ⟨locals, [.value v, .value v, .set idx]⟩) :
    native P ⟨s, (currentFrame decl locals).toCore, (Body.running (saved ++ [v]) (.tee idx :: rest)).render coreAdmin⟩
      ⟨s, (currentFrame decl locals).toCore, (Body.running (saved ++ [v, v]) (.set idx :: rest)).render coreAdmin⟩ := by
  have move := Locals.core_sound (P := P) (s := s) (m := decl.module.toCore) write
  have lifted := Wasm.SingleThreaded.Det.lift_instrs (saved.map Value.toCore) (rest.map coreAdmin.emit) _ _ move
  rcases v with ⟨t, bits⟩
  cases t <;> simp [Locals.coreConfig, Locals.Codec.encode, Locals.coreCodec, Locals.coreInstr,
    Execution.Runtime.Frame.toCore, currentFrame, Body.render, coreAdmin, coreEmit, Op.emit, coreCodeSyntax,
    coreValues, vals, List.map_append, List.append_assoc, Function.comp_def] at lifted ⊢ <;> exact lifted

private theorem entry_iff {H : Type} {P : Profile} {s : Store H} {caller : Runtime.Frame}
    {fn : Function} {target : CallTarget} {saved args : List Value} {rest : List Admin} {dst : Config H}
    (declared : fn.declaration = target.declaration)
    (alloc : s.funcs[target.address.value]? = some fn.coreInstance)
    (typed : args.map Value.type = fn.declaration.params) :
    native P ⟨s, caller.toCore, coreValues (saved ++ args) ++ .ref (.func target.address.value) ::
        .callRefType target.declaration.type.toDefType :: rest⟩ dst ↔
      dst = ⟨s, caller.toCore, coreValues saved ++
        (Phase.label (fn.declaration.frame args).locals (.running fn.initial fn.code)).render coreAdmin target ++ rest⟩ := by
  have enter := Sequence.wasm_entry_context_iff (P := P) (caller := caller) (saved := saved) (rest := rest) (dst := dst)
    alloc typed
  have init := Sequence.core_frame_forCall fn.declaration.module args fn.declaration.locals
  change Frame.forCall fn.declaration.module.toCore (args.map Value.toCore) fn.coreFunc.locals =
    (fn.declaration.frame args).toCore at init
  rw [init, expression_code] at enter
  rw [Phase.render, Phase.renderAt, ← declared]
  simpa only [List.append_assoc, List.singleton_append, coreAdmin, LabelKind.arity, LabelKind.cont, Declaration.type, currentFrame, Declaration.frame] using enter

private theorem running_stays {n : Nat} {cont : List Instr} {v : List Value} {op : Op} {rest : List Op} {out : List Admin}
    (notBranch : ∀ depth result, op ≠ .br depth result)
    (notReturn : op ≠ .return_)
    (pop : LabelExit n cont ((Body.running v (op :: rest)).render coreAdmin) out) : False := by
  change LabelExit n cont (coreValues v ++ coreAdmin.emit op :: rest.map coreAdmin.emit) out at pop
  cases op with
  | numeric p =>
    cases p <;> exact Computed.core_label_stays (head := coreAdmin.emit (.numeric _)) (by rfl)
      (by simp [coreAdmin, coreEmit, Prefix.emit, coreSyntax])
      (by simp [coreAdmin, coreEmit, Prefix.emit, coreSyntax])
      (by simp [coreAdmin, coreEmit, Prefix.emit, coreSyntax, Admin.IsReturnCallRef])
      (by simp [coreAdmin, coreEmit, Prefix.emit, coreSyntax])
      (by simp [coreAdmin, coreEmit, Prefix.emit, coreSyntax]) pop
  | set idx =>
    exact Computed.core_label_stays (head := .plain (.localSet idx)) rfl
      (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) pop
  | tee idx =>
    exact Computed.core_label_stays (head := .plain (.localTee idx)) rfl
      (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) pop
  | call t =>
    exact Computed.core_label_stays (head := .plain (.call t.index)) rfl
      (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) pop
  | if_ result thenBody elseBody =>
    exact Computed.core_label_stays (head := coreAdmin.emit (.if_ result thenBody elseBody)) rfl
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax, Admin.IsReturnCallRef])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax]) pop
  | indexedIf index signature thenBody elseBody =>
    exact Computed.core_label_stays (head := coreAdmin.emit (.indexedIf index signature thenBody elseBody)) rfl
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax, Admin.IsReturnCallRef])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax]) pop
  | block result body =>
    exact Computed.core_label_stays (head := coreAdmin.emit (.block result body)) rfl
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax, Admin.IsReturnCallRef])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax]) pop
  | loop result body =>
    exact Computed.core_label_stays (head := coreAdmin.emit (.loop result body)) rfl
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax, Admin.IsReturnCallRef])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax]) pop
  | indexedLoop index signature body =>
    exact Computed.core_label_stays (head := coreAdmin.emit (.indexedLoop index signature body)) rfl
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax, Admin.IsReturnCallRef])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax]) pop
  | indexedBlock index signature body =>
    exact Computed.core_label_stays (head := coreAdmin.emit (.indexedBlock index signature body)) rfl
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax, Admin.IsReturnCallRef])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax])
      (by simp [coreAdmin, coreEmit, Op.emit, coreCodeSyntax]) pop
  | brTable depths fallback _ =>
    exact Computed.core_label_stays (head := .plain (.brTable depths fallback)) rfl
      (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) pop
  | brIf depth _ =>
    exact Computed.core_label_stays (head := .plain (.brIf depth)) rfl
      (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) pop
  | br depth result => exact notBranch depth result rfl
  | return_ => exact notReturn rfl
  | unreachable =>
    exact Computed.core_label_stays (head := .plain .unreachable) rfl
      (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) pop

private theorem active_entered_iff {H : Type} {P : Profile} {s : Store H} {program : Program} (n : Nat) {kind : LabelKind}
    {caller : Runtime.Frame} {root target : CallTarget} {fn : Function}
    (found : program.lookup root.address = some fn) (used : target ∈ fn.targets)
    {locals saved : List Value} {rest : List Op} {child : Phase} (live : child.Active)
    {k : Nat} {f : Frame} {code : List Admin} (rendered : child.render coreAdmin target = [.frame k f code])
    (childStep : ∀ {dst}, native P (coreConfig s (currentFrame root.declaration locals) target child) dst ↔
      ∃ out, program.FrameEdge target.address child out ∧ dst = coreConfig s (currentFrame root.declaration locals) target out)
    {dst : Config H} :
    native P (coreAt s caller root n (.label locals (.active saved target child rest)) kind) dst ↔
      ∃ out, program.FrameEdgeAt root.address kind (.label locals (.active saved target child rest)) out ∧
        dst = coreAt s caller root n out kind := by
  have ctx : native P (coreAt s caller root n (.label locals (.active saved target child rest)) kind) dst ↔
      ∃ mid, native P (coreConfig s (currentFrame root.declaration locals) target child) mid ∧
        dst = ⟨mid.store, caller.toCore, [.frame n mid.frame
          [.label (kind.arity n) (kind.cont coreCodeSyntax) (coreValues saved ++ mid.code ++ rest.map coreAdmin.emit)]]⟩ := by
    change native P ⟨s, caller.toCore, [.frame n (currentFrame root.declaration locals).toCore
        [.label (kind.arity n) (kind.cont coreCodeSyntax) (coreValues saved ++ child.render coreAdmin target ++ rest.map coreAdmin.emit)]]⟩ dst ↔
      ∃ mid, native P ⟨s, (currentFrame root.declaration locals).toCore, child.render coreAdmin target⟩ mid ∧
        dst = ⟨mid.store, caller.toCore, [.frame n mid.frame
          [.label (kind.arity n) (kind.cont coreCodeSyntax) (coreValues saved ++ mid.code ++ rest.map coreAdmin.emit)]]⟩
    rw [rendered, List.append_assoc, List.singleton_append]
    exact core_entered_child_iff (saved := saved.map Value.toCore)
  rw [ctx]
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨out, childEdge, rfl⟩ := childStep.mp move
    refine ⟨.label locals (Body.attach saved target rest out),
      (frame_active_iff found used live (kind := kind)).mpr ⟨out, childEdge, rfl⟩, ?_⟩
    change _ = (⟨s, caller.toCore, [.frame n _ [.label (kind.arity n) (kind.cont coreCodeSyntax) ((Body.attach saved target rest out).render coreAdmin)]]⟩ : Config H)
    rw [attach_code]
    rfl
  · rintro ⟨out, move, rfl⟩
    obtain ⟨childOut, childEdge, rfl⟩ := (frame_active_iff found used live (kind := kind)).mp move
    refine ⟨_, childStep.mpr ⟨childOut, childEdge, rfl⟩, ?_⟩
    change (⟨s, caller.toCore, [.frame n _ [.label (kind.arity n) (kind.cont coreCodeSyntax) ((Body.attach saved target rest childOut).render coreAdmin)]]⟩ : Config H) = _
    rw [attach_code]
    rfl

private theorem under_label_iff {H : Type} {P : Profile} {s : Store H} {caller : Runtime.Frame} {parent : Frame} {n k : Nat} {cont : List Instr}
    {code : List Admin} {dst : Config H}
    (stays : ∀ {out}, LabelExit k cont code out → False) :
    native P ⟨s, caller.toCore, [.frame n parent [.label k cont code]]⟩ dst ↔
      ∃ mid : Config H, native P ⟨s, parent, code⟩ mid ∧
        dst = ⟨mid.store, caller.toCore, [.frame n mid.frame [.label k cont mid.code]]⟩ := by
  constructor
  · intro move
    rcases Computed.core_body_step_cases move with inside | ⟨_, pop, _⟩
    · exact inside
    · exact (stays pop).elim
  · rintro ⟨⟨_, _, _⟩, move, rfl⟩
    exact .ctxtFrame (.ctxtLabel move)

private theorem pending_child_iff {H : Type} {P : Profile} {s : Store H} {program : Program} (n : Nat) {kind : LabelKind}
    (allocated : program.CoreAllocated s) {caller : Runtime.Frame} {root target : CallTarget} {fn callee : Function}
    (found : program.lookup root.address = some fn) (used : target ∈ fn.targets)
    (childFound : program.lookup target.address = some callee) (declared : callee.declaration = target.declaration)
    {locals saved operands : List Value} {rest : List Op} (typed : operands.map Value.type = callee.declaration.params)
    {dst : Config H} :
    native P (coreAt s caller root n (.label locals (.active saved target (.invoke operands) rest)) kind) dst ↔
      ∃ out, program.FrameEdgeAt root.address kind (.label locals (.active saved target (.invoke operands) rest)) out ∧
        dst = coreAt s caller root n out kind := by
  let head := Admin.callRefType target.declaration.type.toDefType
  let ref := Val.ref (.func target.address.value)
  have stays {out : List Admin} (pop : LabelExit (kind.arity n) (kind.cont coreCodeSyntax)
      (coreValues (saved ++ operands) ++ .ref (.func target.address.value) :: head :: rest.map coreAdmin.emit) out) :
      False := by
    have prefixed : vals ((saved ++ operands).map Value.toCore ++ [ref]) ++ head :: rest.map coreAdmin.emit =
        coreValues (saved ++ operands) ++ .ref (.func target.address.value) :: head :: rest.map coreAdmin.emit := by
      rw [vals_append, List.append_assoc]
      rfl
    rw [← prefixed] at pop
    exact Computed.core_label_stays (head := head) rfl (by simp [head]) (by simp [head])
      (by simp [head, Admin.IsReturnCallRef]) (by simp [head]) (by simp [head]) pop
  have ctx := under_label_iff (n := n) (P := P) (s := s) (caller := caller)
    (parent := (currentFrame root.declaration locals).toCore) (dst := dst) stays
  have entry {mid : Config H} := entry_iff (P := P) (caller := currentFrame root.declaration locals) (saved := saved)
    (rest := rest.map coreAdmin.emit) (dst := mid) declared (allocated _ _ childFound) typed
  have live : (Phase.invoke operands).Active := trivial
  have source : (Body.active saved target (.invoke operands) rest).render coreAdmin =
      coreValues (saved ++ operands) ++ .ref (.func target.address.value) :: head :: rest.map coreAdmin.emit := by
    change coreValues saved ++ (coreValues operands ++ [.ref (.func target.address.value), head]) ++ rest.map coreAdmin.emit = _
    rw [values_append]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  change native P ⟨s, caller.toCore, [.frame n _ [.label (kind.arity n) (kind.cont coreCodeSyntax) ((Body.active saved target (.invoke operands) rest).render coreAdmin)]]⟩ dst ↔ _
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

private theorem trapped_not_final {n : Nat} {cont : List Instr} {stack : List Value} {rest : List Op}
    {out : List Admin} (pop : LabelExit n cont ((Body.trapped stack rest).render coreAdmin) out) :
    stack = [] ∧ rest = [] := by
  by_contra unfinished
  exact Computed.core_label_stays (head := .trap) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef])
    (by simp) (fun _ => by simpa using not_and_or.mp unfinished) pop

private theorem sequence_label_iff {H : Type} {P : Profile} {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {saved : List Value} {body rest : List Admin} {dst : Config H} :
    native P ⟨s, f, coreValues saved ++ .label n cont body :: rest⟩ dst ↔
      ∃ mid, native P ⟨s, f, [.label n cont body]⟩ mid ∧
        dst = ⟨mid.store, mid.frame, coreValues saved ++ mid.code ++ rest⟩ := by
  constructor
  · exact Step.ctx_in_seq (vs := saved.map Value.toCore) (by simp [Admin.IsCtx])
  · rintro ⟨⟨_, _, _⟩, move, rfl⟩
    simpa only [List.append_assoc, List.singleton_append] using
      Sim.Step.vals_left (Sim.Step.append_right move rest) (saved.map Value.toCore)

private def inFrame {H : Type} (outer : Frame) (n : Nat) (q : Config H) : Config H :=
  ⟨q.store, outer, [.frame n q.frame q.code]⟩

private theorem inFrame_injective {H : Type} (outer : Frame) (n : Nat) :
    Function.Injective (inFrame (H := H) outer n) := by
  intro a b eq
  cases a
  cases b
  simp_all [inFrame]

private theorem label_frame_iff {H : Type} {P : Profile} {s : Store H} {outer inner : Frame}
    {n k : Nat} {cont : List Instr} {body : List Admin} {dst : Config H} :
    native P (inFrame outer n ⟨s, inner, [.label k cont body]⟩) dst ↔
      ∃ mid, native P ⟨s, inner, [.label k cont body]⟩ mid ∧ dst = inFrame outer n mid := by
  constructor
  · intro move
    rcases Computed.core_body_step_cases move with ⟨mid, inside, rfl⟩ | ⟨out, pop, rfl⟩
    · exact ⟨_, .ctxtLabel inside, rfl⟩
    · refine ⟨⟨s, inner, out⟩, ?_, rfl⟩
      have leave := (Blocks.Context.core_label_cont_iff (P := P) (s := s) (f := inner)
        (saved := []) (rest := []) (dst := ⟨s, inner, out⟩)).mpr
          (.inr ⟨out, pop, by simp [vals]⟩)
      simpa only [vals, List.map_nil, List.nil_append] using leave
  · rintro ⟨⟨_, _, _⟩, move, rfl⟩
    exact .ctxtFrame move

private theorem branch_step_iff {H : Type} {P : Profile} {s : Store H} {program : Program}
    {caller : Runtime.Frame} {target : CallTarget} {fn : Function}
    (found : program.lookup target.address = some fn) {fallthrough : List NumType} {enclosing : EnclosingLabels}
    {kind : LabelKind} {locals stack : List Value} {depth : LabelIdx} {result : List NumType} {rest : List Op}
    (typed : fn.WellTyped stack (.br depth result :: rest) fallthrough enclosing kind) {dst : Config H} :
    native P (coreAt s caller target fallthrough.length (.label locals (.running stack (.br depth result :: rest))) kind) dst ↔
      ∃ out, program.FrameEdgeAt target.address kind (.label locals (.running stack (.br depth result :: rest))) out ∧
        dst = coreAt s caller target fallthrough.length out kind := by
  let n := fallthrough.length
  change native P (inFrame caller.toCore n ⟨s, (currentFrame target.declaration locals).toCore,
    [.label (kind.arity n) (kind.cont coreCodeSyntax) (coreValues stack ++ .plain (.br depth) :: rest.map coreAdmin.emit)]⟩) dst ↔ _
  rw [label_frame_iff]
  have rule {a b : Phase} := frame_edge_iff (a := a) (b := b) (kind := kind) found
  have invert {mid : Config H} := BranchExit.core_label_br_cont_iff (P := P) (s := s)
    (f := (currentFrame target.declaration locals).toCore) (stack := stack.map Value.toCore)
    (n := kind.arity n) (cont := kind.cont coreCodeSyntax) (depth := depth) (rest := rest.map coreAdmin.emit) (dst := mid)
  have deliver (payload : List Value) (size : payload.length = kind.arity n) :
      coreAt s caller target n (kind.branchHere locals payload) kind =
        inFrame caller.toCore n ⟨s, (currentFrame target.declaration locals).toCore, vals (payload.map Value.toCore) ++ expression (kind.cont coreCodeSyntax)⟩ := by
    cases kind with
    | exit | indexed => simp [coreAt, Phase.renderAt, LabelKind.branchHere, LabelKind.cont,
        inFrame, Nested.resultCode, coreAdmin, expression]
    | loop result original =>
      have empty : payload = [] := List.eq_nil_of_length_eq_zero size
      subst payload
      rfl
    | indexedLoop => rfl
  constructor
  · rintro ⟨mid, move, rfl⟩
    rcases invert.mp move with ⟨extra, payload, split, size, here, rfl⟩ | ⟨outer, rfl⟩
    · obtain ⟨extraValues, payload, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp split
      have count : payload.length = kind.arity fallthrough.length := by simpa using size
      obtain rfl : depth = ⟨0⟩ := Idx.toNat_injective here
      have arity := count.trans ((LabelKind.inputs_length kind fallthrough).symm.trans
        (congrArg List.length (branch_here_result (checked_branch typed).1)))
      exact ⟨_, rule.mpr (.branchHere locals extraValues payload result rest arity), (deliver payload count).symm⟩
    · exact ⟨_, rule.mpr (.branchOuter locals stack depth result rest outer), rfl⟩
  · rintro ⟨out, edge, rfl⟩
    cases rule.mp edge with
    | branchHere _ extra payload _ _ arity =>
      have size := arity.trans ((congrArg List.length (branch_here_result (checked_branch typed).1)).symm.trans
        (LabelKind.inputs_length kind fallthrough))
      exact ⟨_, invert.mpr (.inl ⟨extra.map Value.toCore, payload.map Value.toCore, List.map_append, by simpa using size, rfl, rfl⟩), deliver payload size⟩
    | branchOuter _ _ _ _ _ outer =>
      exact ⟨_, invert.mpr (.inr ⟨outer, rfl⟩), rfl⟩

private theorem block_step_iff {H : Type} {P : Profile} {s : Store H} {program : Program}
    {caller : Runtime.Frame} {target : CallTarget} {fn : Function}
    (found : program.lookup target.address = some fn) {n : Nat} {kind innerKind : LabelKind} {locals saved : List Value} {result : Option NumType}
    {inner : Body} {rest : List Op}
    (compatible : ∀ r original, innerKind = .loop r original → r = result)
    (edgeView : ∀ {out}, program.FrameEdgeAt target.address kind (.label locals (inner.underLabel saved result rest innerKind)) out ↔
      ∃ next, program.FrameEdgeAt target.address innerKind (.label locals inner) next ∧
        out = next.afterBlock saved result rest innerKind)
    (inside : ∀ {dst}, native P (coreAt s caller target (innerKind.results result).length (.label locals inner) innerKind) dst ↔
      ∃ next, program.FrameEdgeAt target.address innerKind (.label locals inner) next ∧
        dst = coreAt s caller target (innerKind.results result).length next innerKind)
    {dst : Config H} :
    native P (coreAt s caller target n (.label locals (inner.underLabel saved result rest innerKind)) kind) dst ↔
      ∃ out, program.FrameEdgeAt target.address kind (.label locals (inner.underLabel saved result rest innerKind)) out ∧
        dst = coreAt s caller target n out kind := by
  let k := (innerKind.results result).length
  let code := coreValues saved ++ (.label (innerKind.arity k) (innerKind.cont coreCodeSyntax) (inner.render coreAdmin) : Admin) :: rest.map coreAdmin.emit
  have stays {out} (pop : LabelExit (kind.arity n) (kind.cont coreCodeSyntax) code out) : False := by
    exact Computed.core_label_stays (head := .label (innerKind.arity k) (innerKind.cont coreCodeSyntax) (inner.render coreAdmin)) rfl
      (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) pop
  have shape :
      coreAt s caller target n (.label locals (inner.underLabel saved result rest innerKind)) kind =
        ⟨s, caller.toCore, [.frame n (currentFrame target.declaration locals).toCore [.label (kind.arity n) (kind.cont coreCodeSyntax) code]]⟩ := by
    rw [coreAt, Phase.renderAt, render_under_label coreAdmin saved result rest innerKind compatible]
    rfl
  rw [shape, under_label_iff stays]
  have render {next} (edge : program.FrameEdgeAt target.address innerKind (.label locals inner) next) :=
    render_block coreAdmin values_append rfl target n saved result rest kind innerKind compatible next
      (label_outcome ((frame_edge_iff found).mp edge) ⟨_, _, rfl⟩)
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨branch, step, rfl⟩ := (sequence_label_iff (saved := saved)).mp move
    have lifted : native P (coreAt s caller target k (.label locals inner) innerKind) (inFrame caller.toCore k branch) := .ctxtFrame step
    obtain ⟨next, edge, eq⟩ := inside.mp lifted
    obtain ⟨ls, code, before, after⟩ := render edge
    have related : inFrame caller.toCore k (⟨s, (currentFrame target.declaration ls).toCore, code⟩ : Config H) =
        coreAt s caller target k next innerKind := by rw [coreAt, before]; rfl
    have same := inFrame_injective caller.toCore k (eq.trans related.symm)
    subst branch
    exact ⟨_, edgeView.mpr ⟨next, edge, rfl⟩, by rw [coreAt, after]; rfl⟩
  · rintro ⟨out, edge, rfl⟩
    obtain ⟨next, move, rfl⟩ := edgeView.mp edge
    have lifted := inside.mpr ⟨next, move, rfl⟩
    obtain ⟨branch, step, eq⟩ := label_frame_iff.mp lifted
    obtain ⟨ls, code, before, after⟩ := render move
    have related : coreAt s caller target k next innerKind =
        inFrame caller.toCore k (⟨s, (currentFrame target.declaration ls).toCore, code⟩ : Config H) := by
      rw [coreAt, before]; rfl
    have same := inFrame_injective caller.toCore k (eq.symm.trans related)
    subst branch
    refine ⟨_, (sequence_label_iff (saved := saved)).mpr ⟨_, step, rfl⟩, ?_⟩
    rw [coreAt, after]
    rfl

private theorem indexed_entry_iff {H : Type} {P : Profile} {s : Store H} {decl : Declaration}
    {locals saved args : List Value} {index : TypeIdx} {signature : Wasm.V1.FuncType}
    {body : List Instr} {rest : List Admin} {dst : Config H}
    (resolved : decl.module.types[index.toNat]? = some signature)
    (typed : args.map Value.type = signature.params) :
    native P ⟨s, (currentFrame decl locals).toCore, vals ((saved ++ args).map Value.toCore) ++
      .plain (.block (.typeIdx index) body) :: rest⟩ dst ↔
      dst = ⟨s, (currentFrame decl locals).toCore, vals (saved.map Value.toCore) ++
        .label signature.results.length [] (vals (args.map Value.toCore) ++ expression body) :: rest⟩ := by
  have lookup : decl.module.toCore.blockType? (.typeIdx index) =
      some (signature.params.map Validation.Ty.num, signature.results.map Validation.Ty.num) := by
    rw [Blocks.Indexed.core_type_idx, resolved]
    rfl
  have arity : args.length = signature.params.length := by simpa using congrArg List.length typed
  rw [show native P = Step P noHost from rfl, Blocks.core_block_step_iff]
  constructor
  · rintro ⟨kept, used, params, results, split, found, size, rfl⟩
    change decl.module.toCore.blockType? (.typeIdx index) = _ at found
    rw [lookup] at found
    cases found
    rw [List.map_append] at split
    have count : (args.map Value.toCore).length = used.length := by simpa [arity] using size.symm
    obtain ⟨rfl, rfl⟩ := List.append_inj' split count
    simp
  · intro eq
    exact ⟨(saved.map Value.toCore), (args.map Value.toCore), _, _, List.map_append, lookup, by simpa using arity,
      by simpa using eq⟩

private theorem indexed_loop_entry_iff {H : Type} {P : Profile} {s : Store H} {decl : Declaration}
    {locals saved args : List Value} {index : TypeIdx} {signature : Wasm.V1.FuncType}
    {body : List Instr} {rest : List Admin} {dst : Config H}
    (resolved : decl.module.types[index.toNat]? = some signature)
    (typed : args.map Value.type = signature.params) :
    native P ⟨s, (currentFrame decl locals).toCore, vals ((saved ++ args).map Value.toCore) ++
      .plain (.loop (.typeIdx index) body) :: rest⟩ dst ↔
      dst = ⟨s, (currentFrame decl locals).toCore, vals (saved.map Value.toCore) ++
        .label signature.params.length [.loop (.typeIdx index) body] (vals (args.map Value.toCore) ++ expression body) :: rest⟩ := by
  have lookup : decl.module.toCore.blockType? (.typeIdx index) =
      some (signature.params.map Validation.Ty.num, signature.results.map Validation.Ty.num) := by
    rw [Blocks.Indexed.core_type_idx, resolved]
    rfl
  have arity : args.length = signature.params.length := by simpa using congrArg List.length typed
  rw [show native P = Step P noHost from rfl, Loops.core_loop_step_iff]
  constructor
  · rintro ⟨kept, used, params, results, split, found, size, rfl⟩
    change decl.module.toCore.blockType? (.typeIdx index) = _ at found
    rw [lookup] at found
    cases found
    rw [List.map_append] at split
    have count : (args.map Value.toCore).length = used.length := by simpa [arity] using size.symm
    obtain ⟨rfl, rfl⟩ := List.append_inj' split count
    simp
  · intro eq
    exact ⟨(saved.map Value.toCore), (args.map Value.toCore), _, _, List.map_append, lookup, by simpa using arity,
      by simpa using eq⟩

private theorem region_step_iff {H : Type} {P : Profile} {s : Store H} {program : Program} (checked : program.checkDirect = true)
    (allocated : program.CoreAllocated s) {caller : Runtime.Frame} {target : CallTarget} {fn : Function}
    (rootFound : program.lookup target.address = some fn)
    (rootDeclared : fn.declaration = target.declaration)
    {bound : Nat}
    (descend : ∀ child, ∀ {parent callee q dst}, sizeOf q < bound →
      Root program parent child callee → Admitted program callee q →
      (native P (coreConfig s parent child q) dst ↔
        ∃ out, program.FrameEdge child.address q out ∧ dst = coreConfig s parent child out))
    (size : Nat) : ∀ {body locals fallthrough enclosing kind dst}, sizeOf body = size → size < bound →
      AdmittedAt program fn fallthrough enclosing (.label locals body) kind →
      (native P (coreAt s caller target fallthrough.length (.label locals body) kind) dst ↔
        ∃ out, program.FrameEdgeAt target.address kind (.label locals body) out ∧
          dst = coreAt s caller target fallthrough.length out kind) := by
  induction size using Nat.strong_induction_on with
  | ind size ih =>
    intro body locals fallthrough enclosing kind dst sizeEq within ready
    let n := fallthrough.length
    let k := kind.arity n
    let cont := kind.cont coreCodeSyntax
    have rule {a b : Phase} := frame_edge_iff (a := a) (b := b) (kind := kind) rootFound
    cases ready with
    | @running _ _ _ _ locals stack rest typed codeTyped =>
      cases rest with
      | nil =>
        constructor
        · intro move
          rcases Computed.core_body_step_cases move with ⟨_, inside, _⟩ | ⟨_, pop, eq⟩
          · exact (Nested.core_result_stuck (r := .values stack) (by simpa only [Body.render, coreAdmin,
              List.map_nil, List.append_nil, Nested.resultCode] using inside)).elim
          · exact ⟨_, rule.mpr (.leaveValues locals stack), eq.trans (by
              have leave := Nested.core_label_result (r := .values stack)
                (by simpa only [Body.render, coreAdmin, List.map_nil, List.append_nil, Nested.resultCode] using pop)
              rw [leave]
              rfl)⟩
        · rintro ⟨out, move, rfl⟩
          cases rule.mp move with
          | leaveValues =>
            simpa only [coreAt, Phase.renderAt, Body.render, coreAdmin, List.map_nil, List.append_nil, Nested.resultCode] using
              Step.ctxtFrame (f := caller.toCore) (n := n)
                (Step.labelVals (P := P) (host := noHost) (cont := cont) (n := k)
                  (vs := stack.map Value.toCore) (s := s) (f := (currentFrame target.declaration locals).toCore))
      | cons op rest =>
        by_cases isBranch : ∃ depth result, op = .br depth result
        · obtain ⟨depth, result, rfl⟩ := isBranch
          exact branch_step_iff (P := P) rootFound codeTyped
        have notBranch depth result (eq : op = .br depth result) : False := isBranch ⟨_, _, eq⟩
        by_cases isReturn : op = .return_
        case pos =>
          subst op
          constructor
          · intro move
            rcases Computed.core_body_step_cases move with ⟨_, inside, _⟩ | ⟨_, pop, eq⟩
            · exact (CallFrame.core_return_stuck (stack := stack.map Value.toCore)
                (tail := rest.map coreAdmin.emit) inside).elim
            · exact ⟨_, rule.mpr (.returnLabel locals stack rest),
                eq.trans (by rw [CallFrame.core_return_label_result pop]; rfl)⟩
          · rintro ⟨out, move, rfl⟩
            cases rule.mp move with
            | returnLabel =>
              simpa only [coreAt, Phase.renderAt, Body.render, coreAdmin, List.map_cons,
                coreEmit, Op.emit, coreCodeSyntax, List.append_assoc, List.singleton_append, n, k, cont] using
                Step.ctxtFrame (f := caller.toCore) (n := n)
                  (Step.returnLabel (P := P) (host := noHost) (s := s)
                    (f := (currentFrame target.declaration locals).toCore)
                    (n := k) (cont := cont)
                    (vs := stack.map Value.toCore) (rest := rest.map coreAdmin.emit))
        have stays {out : List Admin} := running_stays (n := k) (cont := cont) (v := stack) (op := op) (rest := rest) notBranch isReturn (out := out)
        constructor
        · intro move
          obtain ⟨mid, inner, eq⟩ := (under_label_iff stays).mp move
          cases op with
          | br depth result => exact (notBranch depth result rfl).elim
          | return_ => exact (isReturn rfl).elim
          | numeric op =>
            have reduction := (Prefix.core_step_iff (f := currentFrame target.declaration locals) (op := op) (tail := rest.map coreAdmin.emit)).mp inner
            obtain ⟨answer, reduce, rfl⟩ := reduction
            exact ⟨_, rule.mpr (.numeric reduce), eq.trans (by cases answer <;> rfl)⟩
          | set idx =>
            obtain ⟨saved, value, next, rfl, write, rfl⟩ := Computed.core_set_read (f := currentFrame target.declaration locals) inner
            exact ⟨_, rule.mpr (.localSet write), eq⟩
          | tee idx =>
            obtain ⟨saved, value, rfl, write, rfl⟩ := Computed.core_tee_read (f := currentFrame target.declaration locals) inner
            exact ⟨_, rule.mpr (.localTee write), eq⟩
          | call child =>
            obtain ⟨saved, operands, rfl, used, count⟩ := split_call codeTyped
            obtain ⟨callee, childFound, declared, resolves⟩ := linked_direct_target checked rootFound used
            have h : (currentFrame target.declaration locals).module.funcs[child.index.toNat]? = some child.address := by
              simpa only [currentFrame, ← rootDeclared] using resolves
            have call := (Computed.core_direct_call_iff (stack := saved ++ operands)
              (tail := rest.map coreAdmin.emit) h (allocated _ _ childFound)).mp inner
            have signature : (callee.coreInstance (H := H)).type = child.declaration.type.toDefType :=
              congrArg (fun d => d.type.toDefType) declared
            rw [signature] at call
            subst mid
            exact ⟨_, rule.mpr (.dispatch locals saved operands child rest used count), eq.trans (by
              simp only [coreAt, Phase.renderAt, Body.render, coreAdmin, values_append,
                List.append_assoc, List.cons_append, List.nil_append]
              rfl)⟩
          | brTable depths fallback result =>
            obtain ⟨saved, selector, rfl⟩ := Function.split_br_table codeTyped
            have select := (Computed.core_br_table_iff (P := P) (s := s) (f := (currentFrame target.declaration locals).toCore)
              (saved := saved.map Value.toCore) (selector := selector) (depths := depths) (fallback := fallback)
              (rest := rest.map coreAdmin.emit)).mp (by
              simpa only [native, Body.render, coreAdmin, coreEmit, Op.emit, coreCodeSyntax, coreValues,
                List.map_append, List.map_cons, List.map_nil, Value.toCore, Value.int, Val.i32] using inner)
            subst mid
            exact ⟨_, rule.mpr (.branchTable locals saved selector depths fallback result rest), eq⟩
          | brIf depth result =>
            obtain ⟨saved, condition, rfl⟩ := Function.split_br_if codeTyped
            have select := (Computed.core_br_if_iff (P := P) (s := s) (f := (currentFrame target.declaration locals).toCore)
              (saved := saved.map Value.toCore) (condition := condition) (depth := depth) (rest := rest.map coreAdmin.emit)).mp (by
              simpa only [native, Body.render, coreAdmin, coreEmit, Op.emit, coreCodeSyntax, coreValues,
                List.map_append, List.map_cons, List.map_nil, Value.toCore, Value.int] using inner)
            subst mid
            exact ⟨_, rule.mpr (.branchIf locals saved condition depth result rest), eq.trans (by
              simp only [coreAt, Phase.renderAt, Body.render, Op.map_br_if, coreAdmin, coreEmit,
                Op.emit, coreCodeSyntax, List.append_assoc]
              rfl)⟩
          | if_ result thenBody elseBody =>
            obtain ⟨saved, condition, rfl⟩ := Function.split_if codeTyped
            have select := (Computed.core_if_iff (P := P) (s := s) (f := (currentFrame target.declaration locals).toCore)
              (bt := Blocks.coreType result) (saved := saved.map Value.toCore) (condition := condition)
              (thenBody := Op.emitList coreCodeSyntax thenBody)
              (elseBody := Op.emitList coreCodeSyntax elseBody) (rest := rest.map coreAdmin.emit)).mp (by
              simpa only [native, Body.render, coreAdmin, coreEmit, Op.emit, coreCodeSyntax,
                Function.comp_def, coreValues, List.map_append, List.map_cons, List.map_nil, Value.toCore, Value.int] using inner)
            subst mid
            refine ⟨_, rule.mpr (.ifSelect locals saved condition result thenBody elseBody rest), ?_⟩
            exact eq.trans (by
              simp only [coreAt, Phase.renderAt, Body.render, coreAdmin, coreEmit, Op.emit,
                coreCodeSyntax, Function.comp_def, Op.emitList_selected, List.map_cons]
              rfl)
          | indexedIf index signature thenBody elseBody =>
            obtain ⟨saved, condition, rfl⟩ := Function.split_indexed_if codeTyped
            have select := (Computed.core_if_iff (P := P) (s := s) (f := (currentFrame target.declaration locals).toCore)
              (bt := .typeIdx index) (saved := saved.map Value.toCore) (condition := condition)
              (thenBody := Op.emitList coreCodeSyntax thenBody)
              (elseBody := Op.emitList coreCodeSyntax elseBody) (rest := rest.map coreAdmin.emit)).mp (by
              simpa only [native, Body.render, coreAdmin, coreEmit, Op.emit, coreCodeSyntax,
                Function.comp_def, coreValues, List.map_append, List.map_cons, List.map_nil, Value.toCore, Value.int] using inner)
            subst mid
            refine ⟨_, rule.mpr (.indexedIfSelect locals saved condition index signature thenBody elseBody rest), ?_⟩
            exact eq.trans (by
              simp only [coreAt, Phase.renderAt, Body.render, coreAdmin, coreEmit, Op.emit,
                coreCodeSyntax, Function.comp_def, Op.emitList_selected, List.map_cons]
              rfl)
          | block result body =>
            have enter := (Blocks.core_context_entry_iff (result := result)
              (body := Op.emitList coreCodeSyntax body) (saved := stack.map Value.toCore)
              (rest := rest.map coreAdmin.emit)).mp inner
            rw [code_expression] at enter
            exact ⟨_, rule.mpr (.blockEnter locals stack result body rest), eq.trans
              (congrArg (fun x : Config H =>
                (⟨x.store, caller.toCore, [.frame n x.frame [.label k cont x.code]]⟩ : Config H)) enter)⟩
          | indexedBlock index signature body =>
            obtain ⟨saved, args, rfl, typed, resolved⟩ := split_indexed_block codeTyped
            have inModule : target.declaration.module.types[index.toNat]? = some signature := by
              simpa only [← rootDeclared] using resolved
            have enter := (indexed_entry_iff (s := s) (locals := locals) (saved := saved) (args := args)
              (body := Op.emitList coreCodeSyntax body) (rest := rest.map coreAdmin.emit)
              inModule typed).mp inner
            rw [code_expression] at enter
            exact ⟨_, rule.mpr (.indexedBlockEnter locals saved args index signature body rest resolved typed),
              eq.trans (congrArg (fun x : Config H =>
                (⟨x.store, caller.toCore, [.frame n x.frame [.label k cont x.code]]⟩ : Config H)) enter)⟩
          | indexedLoop index signature body =>
            obtain ⟨saved, args, rfl, typed, resolved⟩ := split_indexed_loop codeTyped
            have inModule : target.declaration.module.types[index.toNat]? = some signature := by
              simpa only [← rootDeclared] using resolved
            have enter := (indexed_loop_entry_iff (s := s) (locals := locals) (saved := saved) (args := args)
              (body := Op.emitList coreCodeSyntax body) (rest := rest.map coreAdmin.emit)
              inModule typed).mp inner
            rw [code_expression] at enter
            exact ⟨_, rule.mpr (.indexedLoopEnter locals saved args index signature body rest resolved typed),
              eq.trans (congrArg (fun x : Config H =>
                (⟨x.store, caller.toCore, [.frame n x.frame [.label k cont x.code]]⟩ : Config H)) enter)⟩
          | loop result body =>
            have enter := (Loops.core_entry_iff (result := result)
              (body := Op.emitList coreCodeSyntax body) (saved := stack.map Value.toCore)
              (rest := rest.map coreAdmin.emit)).mp inner
            rw [code_expression] at enter
            exact ⟨_, rule.mpr (.loopEnter locals stack result body rest), eq.trans
              (congrArg (fun x : Config H =>
                (⟨x.store, caller.toCore, [.frame n x.frame [.label k cont x.code]]⟩ : Config H)) enter)⟩
          | unreachable =>
            obtain rfl := (Computed.core_unreachable_iff (stack := stack.map Value.toCore)).mp inner
            exact ⟨_, rule.mpr (.unreachable locals stack rest), eq⟩
        · rintro ⟨out, move, rfl⟩
          cases rule.mp move with
          | branchHere | branchOuter => exact (isBranch ⟨_, _, rfl⟩).elim
          | returnLabel => exact (isReturn rfl).elim
          | @numeric _ locals stack op rest answer reduce =>
            apply lift_label
            exact (Prefix.core_step_iff (P := P) (s := s) (f := currentFrame target.declaration locals) (stack := stack)
              (op := op) (tail := rest.map coreAdmin.emit)).mpr ⟨answer, reduce, by cases answer <;> rfl⟩
          | @localSet _ locals next saved i value rest write =>
            exact lift_label (set_sound write)
          | @localTee _ locals saved i value rest write =>
            exact lift_label (tee_sound write)
          | dispatch _ saved operands child rest used count =>
            obtain ⟨callee, childFound, declared, resolves⟩ := linked_direct_target checked rootFound used
            have h : (currentFrame target.declaration locals).module.funcs[child.index.toNat]? = some child.address := by
              simpa only [currentFrame, ← rootDeclared] using resolves
            have signature : (callee.coreInstance (H := H)).type = child.declaration.type.toDefType :=
              congrArg (fun d => d.type.toDefType) declared
            have step {dst : Config H} := Computed.core_direct_call_iff (P := P) (stack := saved ++ operands)
              (tail := rest.map coreAdmin.emit) (dst := dst) h (allocated _ _ childFound)
            rw [signature] at step
            apply lift_label
            simpa only [Body.render, Phase.render, Phase.renderAt, coreAdmin, coreEmit, Op.emit, coreCodeSyntax, Sequence.coreSource, Function.comp_def,
              values_append, List.map_cons, List.append_assoc, List.cons_append, List.nil_append] using step.mpr rfl
          | branchTable _ saved selector depths fallback result rest =>
            apply lift_label
            have select := (Computed.core_br_table_iff (P := P) (s := s) (f := (currentFrame target.declaration locals).toCore)
              (saved := saved.map Value.toCore) (selector := selector) (depths := depths) (fallback := fallback)
              (rest := rest.map coreAdmin.emit)).mpr rfl
            simpa only [native, Body.render, coreAdmin, coreEmit, Op.emit, coreCodeSyntax,
              List.map_append, List.map_cons, List.map_nil, coreValues, Value.toCore, Value.int, Val.i32] using select
          | branchIf _ saved condition depth result rest =>
            apply lift_label
            have select := (Computed.core_br_if_iff (P := P) (s := s) (f := (currentFrame target.declaration locals).toCore)
              (saved := saved.map Value.toCore) (condition := condition) (depth := depth) (rest := rest.map coreAdmin.emit)).mpr rfl
            simpa only [native, Body.render, Op.map_br_if, coreAdmin, coreEmit, Op.emit, coreCodeSyntax,
              List.append_assoc, List.map_append, List.map_cons, List.map_nil, coreValues, Value.toCore, Value.int] using select
          | @ifSelect _ locals saved condition result thenBody elseBody rest =>
            apply lift_label
            have select := (Computed.core_if_iff (P := P) (s := s) (f := (currentFrame target.declaration locals).toCore)
              (bt := Blocks.coreType result) (saved := saved.map Value.toCore)
              (condition := condition)
              (thenBody := Op.emitList coreCodeSyntax thenBody)
              (elseBody := Op.emitList coreCodeSyntax elseBody) (rest := rest.map coreAdmin.emit)).mpr rfl
            simpa only [native, Body.render, coreAdmin, coreEmit, Op.emit, coreCodeSyntax, Function.comp_def,
              Op.emitList_selected, coreValues, List.map_cons, List.map_append, List.map_nil,
              Value.toCore, Value.int] using select
          | @indexedIfSelect _ locals saved condition index _ thenBody elseBody rest =>
            apply lift_label
            have select := (Computed.core_if_iff (P := P) (s := s) (f := (currentFrame target.declaration locals).toCore)
              (bt := .typeIdx index) (saved := saved.map Value.toCore)
              (condition := condition)
              (thenBody := Op.emitList coreCodeSyntax thenBody)
              (elseBody := Op.emitList coreCodeSyntax elseBody) (rest := rest.map coreAdmin.emit)).mpr rfl
            simpa only [native, Body.render, coreAdmin, coreEmit, Op.emit, coreCodeSyntax, Function.comp_def,
              Op.emitList_selected, coreValues, List.map_cons, List.map_append, List.map_nil,
              Value.toCore, Value.int] using select
          | blockEnter =>
            rename_i result body
            apply lift_label
            exact (Blocks.core_context_entry_iff (result := result) (body := Op.emitList coreCodeSyntax body)
              (saved := stack.map Value.toCore) (rest := rest.map coreAdmin.emit)).mpr (by rw [code_expression]; rfl)
          | indexedBlockEnter locals saved args index signature body rest resolved typed =>
            have inModule : target.declaration.module.types[index.toNat]? = some signature := by
              simpa only [← rootDeclared] using resolved
            apply lift_label
            exact (indexed_entry_iff (saved := saved) (body := Op.emitList coreCodeSyntax body)
              (rest := rest.map coreAdmin.emit) inModule typed).mpr (by rw [code_expression]; rfl)
          | indexedLoopEnter locals saved args index signature body rest resolved typed =>
            have inModule : target.declaration.module.types[index.toNat]? = some signature := by
              simpa only [← rootDeclared] using resolved
            apply lift_label
            exact (indexed_loop_entry_iff (saved := saved) (body := Op.emitList coreCodeSyntax body)
              (rest := rest.map coreAdmin.emit) inModule typed).mpr (by rw [code_expression]; rfl)
          | loopEnter =>
            rename_i result body
            apply lift_label
            exact (Loops.core_entry_iff (result := result) (body := Op.emitList coreCodeSyntax body)
              (saved := stack.map Value.toCore) (rest := rest.map coreAdmin.emit)).mpr (by rw [code_expression]; rfl)
          | unreachable =>
            exact lift_label (Computed.core_unreachable_iff.mpr rfl)
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
        rcases Computed.core_body_step_cases move with ⟨mid, inside, eq⟩ | ⟨_, pop, eq⟩
        · obtain ⟨kept, remaining, cut, rfl⟩ := (Prefix.core_discard_iff (f := currentFrame target.declaration locals) coreAdmin.emit).mp inside
          exact ⟨_, rule.mpr (.discard cut), eq⟩
        · obtain ⟨rfl, rfl⟩ := trapped_not_final pop
          exact ⟨_, rule.mpr (.leaveTrap locals), eq.trans (by rw [Nested.core_label_result (r := .trap) pop]; rfl)⟩
      · rintro ⟨out, move, rfl⟩
        cases rule.mp move with
        | discard cut => exact lift_label ((Prefix.core_discard_iff (f := currentFrame target.declaration locals) coreAdmin.emit).mpr ⟨_, _, cut, rfl⟩)
        | leaveTrap => exact .ctxtFrame .trapLabel
    | @block _ _ _ _ locals saved result inside rest innerTyped resume =>
      have smaller : sizeOf inside < size := by rw [← sizeEq]; simp [Body.block.sizeOf_spec]; omega
      exact block_step_iff rootFound (P := P) (n := n) (innerKind := .exit)
        (by simp) (block_iff rootFound) (fun {dst} =>
          ih (sizeOf inside) smaller (dst := dst) rfl (smaller.trans within) innerTyped)
    | @indexedBlock _ _ _ _ locals saved signature inside rest innerTyped resume =>
      have smaller : sizeOf inside < size := by rw [← sizeEq]; simp [Body.indexedBlock.sizeOf_spec]; omega
      exact block_step_iff rootFound (P := P) (n := n) (result := none) (innerKind := .indexed signature)
        (by simp) (indexed_block_iff rootFound) (fun {dst} =>
          ih (sizeOf inside) smaller (dst := dst) rfl (smaller.trans within) innerTyped)
    | @loop _ _ _ _ locals saved result original inside rest innerTyped _ resume =>
      have smaller : sizeOf inside < size := by rw [← sizeEq]; simp [Body.loop.sizeOf_spec]; omega
      exact block_step_iff rootFound (P := P) (n := n) (innerKind := .loop result original)
        (fun _ _ eq => (LabelKind.loop.inj eq).1.symm) (loop_iff rootFound) (fun {dst} =>
          ih (sizeOf inside) smaller (dst := dst) rfl (smaller.trans within) innerTyped)
    | @indexedLoop _ _ _ _ locals saved index signature original inside rest innerTyped _ _ resume =>
      have smaller : sizeOf inside < size := by rw [← sizeEq]; simp [Body.indexedLoop.sizeOf_spec]; omega
      exact block_step_iff rootFound (P := P) (n := n) (innerKind := .indexedLoop index signature original)
        (fun _ _ eq => by cases eq) (indexed_loop_iff rootFound) (fun {dst} =>
          ih (sizeOf inside) smaller (dst := dst) rfl (smaller.trans within) innerTyped)

theorem resolved_frame_step_iff {H : Type} {P : Profile} {s : Store H} {program : Program} (checked : program.checkDirect = true)
    (allocated : program.CoreAllocated s) (size : Nat) :
    ∀ {caller target fn a dst}, sizeOf a = size →
      (program.lookup target.address = some fn) → (fn.declaration = target.declaration) →
      (∀ args, a = .call args → target.Resolves caller) → Admitted program fn a →
      (Step P noHost (coreConfig s caller target a) dst ↔
        ∃ out, program.FrameEdge target.address a out ∧ dst = coreConfig s caller target out) := by
  induction size using Nat.strong_induction_on with
  | ind size ih =>
    intro caller target fn a dst sizeEq found declared resolves ready
    have rule {a b : Phase} := frame_edge_iff (a := a) (b := b) (kind := .exit) found
    have alloc := allocated _ _ found
    have coreType : (fn.coreInstance (H := H)).type = target.declaration.type.toDefType :=
      congrArg (fun d => d.type.toDefType) declared
    have descend child {parent callee q dst} (smaller : sizeOf q < size)
        (childRoot : Root program parent child callee) (childReady : Admitted program callee q) :=
      ih (sizeOf q) smaller (dst := dst) rfl childRoot.found childRoot.declared (fun _ _ => childRoot.resolves) childReady
    have region {locals body} (eq : sizeOf (Phase.label locals body) = size)
        (ok : Admitted program fn (.label locals body)) :
        native P (coreConfig s caller target (.label locals body)) dst ↔
          ∃ out, program.FrameEdge target.address (.label locals body) out ∧ dst = coreConfig s caller target out := by
      have bound : sizeOf body < size := by
        simp only [Phase.label.sizeOf_spec] at eq
        omega
      simpa only [coreConfig, coreAt, Phase.render, declared] using
        region_step_iff (P := P) checked allocated found declared descend (sizeOf body) (dst := dst) rfl bound ok
    cases ready with
    | @call _ args typed =>
      have callLookup := resolves args rfl
      have move {next : Config H} := Computed.core_direct_call_iff (s := s) (P := P) (stack := args)
        (tail := []) (dst := next) callLookup alloc
      constructor
      · intro h
        refine ⟨_, rule.mpr (.resolve args), ?_⟩
        rw [coreType] at move
        exact move.mp h
      · rintro ⟨out, h, rfl⟩
        cases rule.mp h with
        | resolve =>
          rw [coreType] at move
          exact move.mpr rfl
    | @invoke _ args typed =>
      have move {next : Config H} := entry_iff (P := P) (caller := caller) (saved := []) (rest := []) (dst := next)
        declared alloc typed
      constructor
      · intro step
        refine ⟨_, rule.mpr (.enter args typed), ?_⟩
        exact (move.mp step).trans (by simp [coreValues, vals, coreConfig])
      · rintro ⟨out, step, rfl⟩
        cases rule.mp step with
        | enter =>
          change native P ⟨s, caller.toCore, coreValues args ++
              [.ref (.func target.address.value), .callRefType target.declaration.type.toDefType]⟩
            ⟨s, caller.toCore, (Phase.label (fn.declaration.frame args).locals (.running fn.initial fn.code)).render coreAdmin target⟩
          simpa only [coreValues, vals, List.map_nil, List.nil_append, List.append_nil] using move.mpr rfl
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
        have frame := CallFrame.core_return_frame_iff (P := P) (s := s) (outer := caller.toCore)
          (inner := (currentFrame target.declaration locals).toCore) (dst := dst)
          (extra := extra.map Value.toCore) (results := results.map Value.toCore) (by simpa using count)
        exact ⟨_, rule.mpr (.returnFrame locals extra results arity),
          frame.mp (by simpa only [coreConfig, Phase.render, Phase.renderAt, coreAdmin, coreValues, List.map_append] using move)⟩
      · rintro ⟨out, move, rfl⟩
        cases rule.mp move with
        | returnFrame locals dropped returned arity =>
          have n := arity.trans (congrArg (fun d => d.results.length) declared)
          simpa only [coreConfig, Phase.render, Phase.renderAt, coreAdmin, coreValues, List.map_append, Nested.resultCode] using
            (CallFrame.core_return_frame_iff (P := P) (s := s) (outer := caller.toCore)
              (inner := (currentFrame target.declaration locals).toCore)
              (extra := dropped.map Value.toCore) (results := returned.map Value.toCore)
              (n := target.declaration.results.length) (by simpa using n)).mpr rfl
    | @exit _ _ _ _ locals result typed outTyped =>
      constructor
      · intro move
        exact ⟨_, rule.mpr (.leaveFrame locals result outTyped), Nested.core_frame_result (caller := caller) (r := result) move⟩
      · rintro ⟨out, move, rfl⟩
        cases rule.mp move with
        | leaveFrame =>
          cases result with
          | trap => exact .trapFrame
          | values xs =>
            exact .frameVals (vs := xs.map Value.toCore) (by
              simpa using (result_length outTyped).trans (congrArg (fun d => d.results.length) declared))
    | branching _ target _ => simp at target
    | @done _ _ _ _ result typed =>
      constructor
      · intro step
        exact (Nested.core_result_stuck (r := result) step).elim
      · rintro ⟨_, step, _⟩
        cases rule.mp step

theorem frame_step_iff {H : Type} {P : Profile} {s : Store H} {program : Program} (checked : program.checkDirect = true)
    (allocated : program.CoreAllocated s) (size : Nat) :
    ∀ {caller target fn a dst}, sizeOf a = size →
      Root program caller target fn → Admitted program fn a →
      (Step P noHost (coreConfig s caller target a) dst ↔
        ∃ out, program.FrameEdge target.address a out ∧ dst = coreConfig s caller target out) :=
  fun sizeEq root => resolved_frame_step_iff checked allocated size sizeEq root.found root.declared
    (fun _ _ => root.resolves)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs.Core
