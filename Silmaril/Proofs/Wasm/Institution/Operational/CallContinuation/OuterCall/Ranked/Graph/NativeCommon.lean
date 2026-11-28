module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs

open Execution.Runtime (FuncAddr Frame Value)
open Computed

theorem split_call {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {kind : LabelKind} {stack : List Value} {target : CallTarget} {rest : List Op}
    (typed : fn.WellTyped stack (.call target :: rest) fallthrough enclosing kind) :
    ∃ saved operands, stack = saved ++ operands ∧ target ∈ fn.targets ∧
      operands.length = target.declaration.params.length := by
  unfold Function.WellTyped at typed
  simp only [checkCode, checkOp, Bool.and_eq_true_iff, decide_eq_true_eq] at typed
  obtain ⟨⟨used, shape⟩, _⟩ := typed
  have length : min target.declaration.params.length stack.length = target.declaration.params.length := by
    simpa [Prefix.stackTypes] using congrArg List.length shape
  have enough : target.declaration.params.length ≤ stack.length := by omega
  let below := stack.length - target.declaration.params.length
  exact ⟨stack.take below, stack.drop below, (List.take_append_drop below stack).symm, used,
    by simp [below]; omega⟩

theorem split_indexed_block {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels}
    {kind : LabelKind} {stack : List Value} {index : TypeIdx} {signature : Wasm.V1.FuncType} {body rest : List Op}
    (typed : fn.WellTyped stack (.indexedBlock index signature body :: rest) fallthrough enclosing kind) :
    ∃ saved args, stack = saved ++ args ∧ args.map Value.type = signature.params ∧
      fn.declaration.module.types[index.toNat]? = some signature := by
  simp only [Function.WellTyped, checkCode, checkOp, Bool.and_eq_true_iff, decide_eq_true_eq] at typed
  obtain ⟨⟨⟨resolved, shape⟩, _⟩, _⟩ := typed
  obtain ⟨saved, args, eq, argsTyped⟩ := SuffixTyped.split shape
  exact ⟨saved, args, eq, argsTyped, resolved⟩

theorem split_indexed_loop {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels}
    {kind : LabelKind} {stack : List Value} {index : TypeIdx} {signature : Wasm.V1.FuncType} {body rest : List Op}
    (typed : fn.WellTyped stack (.indexedLoop index signature body :: rest) fallthrough enclosing kind) :
    ∃ saved args, stack = saved ++ args ∧ args.map Value.type = signature.params ∧
      fn.declaration.module.types[index.toNat]? = some signature := by
  simp only [Function.WellTyped, checkCode, checkOp, Bool.and_eq_true_iff, decide_eq_true_eq] at typed
  obtain ⟨⟨⟨resolved, shape⟩, _⟩, _⟩ := typed
  obtain ⟨saved, args, eq, argsTyped⟩ := SuffixTyped.split shape
  exact ⟨saved, args, eq, argsTyped, resolved⟩

theorem split_return {fn : Function} {stack : List Value} (typed : fn.ReturnTyped stack) :
    ∃ extra results, stack = extra ++ results ∧ results.length = fn.declaration.results.length := by
  have length := congrArg List.length typed
  simp only [List.length_take, Prefix.stackTypes, List.length_reverse, List.length_map] at length
  let below := stack.length - fn.declaration.results.length
  exact ⟨stack.take below, stack.drop below, (List.take_append_drop below stack).symm,
    by simp [below]; omega⟩

theorem result_length {fn : Function} {values : List Value} (typed : fn.ResultTyped (.values values)) :
    values.length = fn.declaration.results.length :=
  (List.length_map ..).symm.trans (congrArg List.length typed)

theorem render_attach {A : Type} {ops : Syntax A}
    (append : ∀ xs ys, ops.values (xs ++ ys) = ops.values xs ++ ops.values ys)
    (saved : List Value) (target : CallTarget) (rest : List Op) (child : Phase) :
    (Body.attach saved target rest child).render ops =
      ops.values saved ++ child.render ops target ++ rest.map ops.emit := by
  cases child with
  | done result => cases result <;> simp [Body.attach, Body.render, Phase.render, Phase.renderAt, Nested.resultCode, append]
  | _ => rfl

theorem render_under_label {A : Type} (ops : Syntax A)
    (saved : List Value) (result : Option NumType) (rest : List Op) (kind : LabelKind)
    (compatible : ∀ r original, kind = .loop r original → r = result) (body : Body) :
    (body.underLabel saved result rest kind).render ops =
      ops.values saved ++ ops.label (kind.results result).length kind (body.render ops) :: rest.map ops.emit := by
  cases kind with
  | exit | indexed | indexedLoop => rfl
  | loop r original => cases compatible r original rfl; rfl

theorem render_block {A : Type} (ops : Syntax A)
    (append : ∀ xs ys, ops.values (xs ++ ys) = ops.values xs ++ ops.values ys)
    (ret : ops.emit .return_ = ops.ret) (target : CallTarget) (n : Nat)
    (saved : List Value) (result : Option NumType) (rest : List Op)
    (outerKind innerKind : LabelKind)
    (compatible : ∀ r original, innerKind = .loop r original → r = result) (next : Phase) (outcome : next.LabelOutcome) :
    ∃ locals code, next.renderAt ops target (innerKind.results result).length innerKind =
        [ops.frame (innerKind.results result).length (currentFrame target.declaration locals) code] ∧
      (next.afterBlock saved result rest innerKind).renderAt ops target n outerKind =
        [ops.frame n (currentFrame target.declaration locals)
          [ops.label n outerKind (ops.values saved ++ code ++ rest.map ops.emit)]] := by
  cases next with
  | call | invoke | done => cases outcome
  | label locals body =>
    exact ⟨locals, _, rfl, by
      rw [Phase.afterBlock, Phase.renderAt, render_under_label ops saved result rest innerKind compatible]
      simp only [List.append_assoc, List.singleton_append]⟩
  | branching locals stack depth result =>
    exact ⟨locals, _, rfl, by
      simp [Phase.afterBlock, Phase.renderAt, Body.render, append, List.append_assoc]⟩
  | returning locals stack =>
    exact ⟨locals, _, rfl, by
      simp [Phase.afterBlock, Phase.renderAt, Body.render, append, ret, List.append_assoc]⟩
  | restart locals result original =>
    exact ⟨locals, _, rfl, by
      simp [Phase.afterBlock, Phase.renderAt, Body.render, List.append_assoc]⟩
  | indexedRestart locals args index signature original =>
    exact ⟨locals, _, rfl, by
      simp [Phase.afterBlock, Phase.renderAt, Body.render, append, List.append_assoc]⟩
  | exit locals result =>
    cases result with
    | values => exact ⟨locals, _, rfl, by simp [Phase.afterBlock, Phase.renderAt, Body.render,
        Nested.resultCode, append, List.append_assoc]⟩
    | trap => exact ⟨locals, _, rfl, by simp only [Phase.afterBlock, Phase.renderAt, Body.render,
      Nested.resultCode, List.append_assoc, List.singleton_append]⟩

private theorem run_correspondence {C : Type} {edge : Phase → Phase → Prop}
    (admitted : Phase → Prop) (admittedStep : ∀ {a b}, admitted a → edge a b → admitted b)
    (render : Phase → C) (native : C → C → Prop)
    (invariant : Phase → Prop)
    (preserved : ∀ {a b}, edge a b → invariant a → invariant b)
    (one : ∀ {a b}, admitted a → invariant a → (native (render a) b ↔
      ∃ out, edge a out ∧ b = render out))
    {a : Phase} {b : C} (ready : admitted a) (supported : invariant a) :
    Relation.ReflTransGen native (render a) b ↔
      ∃ out, Relation.ReflTransGen edge a out ∧ admitted out ∧ b = render out := by
  constructor
  · intro run
    have trace : ∃ out, Relation.ReflTransGen edge a out ∧ admitted out ∧
        invariant out ∧ b = render out := by
      induction run with
      | refl => exact ⟨a, .refl, ready, supported, rfl⟩
      | tail _ step ih =>
        obtain ⟨_, path, admitted, compatible, rfl⟩ := ih
        obtain ⟨out, edge, rfl⟩ := (one admitted compatible).mp step
        exact ⟨out, path.tail edge, admittedStep admitted edge,
          preserved edge compatible, rfl⟩
    obtain ⟨out, path, admitted, _, rfl⟩ := trace
    exact ⟨out, path, admitted, rfl⟩
  · rintro ⟨out, run, readyOut, rfl⟩
    clear readyOut
    have trace : Relation.ReflTransGen native (render a) (render out) ∧
        admitted out ∧ invariant out := by
      induction run with
      | refl => exact ⟨.refl, ready, supported⟩
      | tail _ edge ih =>
        obtain ⟨path, admitted, compatible⟩ := ih
        exact ⟨path.tail ((one admitted compatible).mpr ⟨_, edge, rfl⟩),
          admittedStep admitted edge, preserved edge compatible⟩
    exact trace.1

theorem run_iff_of_invariant {C : Type} {program : Program} {checked : program.check = true}
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    (render : Phase → C) (native : C → C → Prop)
    (invariant : Phase → Prop)
    (preserved : ∀ {a b}, program.Edge checked address a b → invariant a → invariant b)
    (one : ∀ {a b}, Admitted program fn a → invariant a → (native (render a) b ↔
      ∃ out, program.Edge checked address a out ∧ b = render out))
    {a : Phase} {b : C} (ready : Admitted program fn a) (supported : invariant a) :
    Relation.ReflTransGen native (render a) b ↔
      ∃ out, program.Runs checked address a out ∧ Admitted program fn out ∧ b = render out :=
  run_correspondence (Admitted program fn) (Program.admitted_step checked found)
    render native invariant preserved one ready supported

theorem run_iff {C : Type} {program : Program} {checked : program.check = true}
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    (render : Phase → C) (native : C → C → Prop)
    (one : ∀ {a b}, Admitted program fn a → (native (render a) b ↔
      ∃ out, program.Edge checked address a out ∧ b = render out))
    {a : Phase} {b : C} (ready : Admitted program fn a) :
    Relation.ReflTransGen native (render a) b ↔
      ∃ out, program.Runs checked address a out ∧ Admitted program fn out ∧ b = render out :=
  run_iff_of_invariant found render native (fun _ => True) (fun _ _ => trivial)
    (fun admitted _ => one admitted) ready trivial

theorem frame_run_iff {C : Type} {program : Program} (checked : program.checkDirect = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    (render : Phase → C) (native : C → C → Prop)
    (one : ∀ {a b}, Admitted program fn a → (native (render a) b ↔
      ∃ out, program.FrameEdge address a out ∧ b = render out))
    {a : Phase} {b : C} (ready : Admitted program fn a) :
    Relation.ReflTransGen native (render a) b ↔
      ∃ out, program.FrameRuns address a out ∧ Admitted program fn out ∧ b = render out :=
  run_correspondence (Admitted program fn) (Program.frame_admitted_step checked found)
    render native (fun _ => True) (fun _ _ => trivial) (fun guard _ => one guard) ready trivial

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs
