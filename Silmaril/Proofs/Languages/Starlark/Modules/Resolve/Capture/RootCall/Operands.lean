module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall

open Silmaril.Languages.Starlark (Binding resolveName)
open Silmaril.Languages.Starlark.Modules (globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (InOrder)
open Silmaril.Languages.Starlark.Functions (Program DeclarationId)
open Silmaril.Languages.Starlark.Functions.Lowering (ClosureRuns EvaluatesWith EvaluatesManyWith)
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve
open Silmaril.Languages.Starlark.Lists (State Outcome)

local notation "ResolvedExpr" => Silmaril.Languages.Starlark.Functions.Lowering.Expr
local notation "Value" => Silmaril.Languages.Starlark.Lists.Value

private def context (globals : List String) : Context := ⟨[], globals⟩

private theorem resolve_operand {globals : List String} {source : SourceExpr} {code : ResolvedExpr}
    (related : Operand globals source code) (initial : List Binding) :
    ∃ final, resolveExpr (context globals) source initial = .ok (code, final) := by
  induction related generalizing initial with
  | @global name legal declared =>
    cases declared with
    | global _ _ member =>
      refine ⟨globalSlot name :: initial, ?_⟩
      rw [resolveExpr.eq_def]
      simp [context, resolveScalar, resolveRead, resolveReadValue, resolveName, legal, member, Except.map, globalSlot]
  | int n =>
    exact ⟨initial, by rw [resolveExpr.eq_def]; rfl⟩
  | string s =>
    exact ⟨initial, by rw [resolveExpr.eq_def]; rfl⟩
  | index _ _ recv sub =>
    obtain ⟨middle, receiver⟩ := recv initial
    obtain ⟨final, index⟩ := sub middle
    refine ⟨final, ?_⟩
    rw [resolveExpr.eq_def]
    simp [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, receiver, index]

theorem resolves_operand {globals : List String} {source : SourceExpr} {code : ResolvedExpr}
    (related : Operand globals source code) :
    ∃ reads, resolveTracked ⟨[], globals⟩ source = .ok (code, reads) := by
  obtain ⟨final, step⟩ := resolve_operand related []
  exact ⟨final.reverse, by simp [resolveTracked, ← show context globals = ⟨[], globals⟩ from rfl, step, Except.map]⟩

private theorem resolve_actuals {globals : List String} {source : List SourceExpr} {codes : List ResolvedExpr}
    (related : InOrder (Operand globals) source codes) (initial : List Binding) :
    ∃ final, (source.mapM (resolveExpr (context globals))) initial = .ok (codes, final) := by
  induction related generalizing initial with
  | nil => exact ⟨initial, rfl⟩
  | cons head _ ih =>
    obtain ⟨middle, first⟩ := resolve_operand head initial
    obtain ⟨final, rest⟩ := ih middle
    refine ⟨final, ?_⟩
    simp [List.mapM_cons, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, first, rest]

theorem resolves_display {globals : List String} {items : List SourceExpr} {codes : List ResolvedExpr}
    (related : InOrder (Operand globals) items codes) :
    ∃ reads, resolveTracked ⟨[], globals⟩ (.list items) = .ok (.list codes, reads) ∧
      resolveTracked ⟨[], globals⟩ (.tuple items) = .ok (.tuple codes, reads) := by
  obtain ⟨final, resolved⟩ := resolve_actuals related []
  have spine : (items.attach.mapM fun arg => resolveExpr (context globals) arg.val) =
      items.mapM (resolveExpr (context globals)) := by
    calc
      _ = (items.attach.map Subtype.val).mapM (resolveExpr (context globals)) := by
        simp only [List.mapM_map, Function.comp_def]
      _ = _ := by rw [List.attach_map_subtype_val]
  refine ⟨final.reverse, ?_, ?_⟩ <;>
    change resolveTracked (context globals) _ = _ <;>
    rw [resolveTracked, resolveExpr.eq_def] <;>
    simp [spine, resolved, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, Except.map]

theorem resolves_call {globals : List String} {callee : SourceExpr} {positional : List SourceExpr}
    {function : ResolvedExpr} {actuals : List ResolvedExpr} (related : Operand globals callee function)
    (arguments : InOrder (Operand globals) positional actuals) :
    ∃ reads, resolveTracked ⟨[], globals⟩ (.call callee positional [] none none) =
      .ok (.call function actuals [] none none, reads) := by
  obtain ⟨middle, first⟩ := resolve_operand related []
  obtain ⟨final, rest⟩ := resolve_actuals arguments middle
  refine ⟨final.reverse, ?_⟩
  change resolveTracked (context globals) _ = _
  rw [resolveTracked, resolveExpr.eq_def]
  have spine : (positional.attach.mapM fun arg => resolveExpr (context globals) arg.val) =
      positional.mapM (resolveExpr (context globals)) := by
    calc
      _ = (positional.attach.map Subtype.val).mapM (resolveExpr (context globals)) := by
        simp only [List.mapM_map, Function.comp_def]
      _ = _ := by rw [List.attach_map_subtype_val]
  simp [spine, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, Except.map, first, rest]

theorem evaluates_operand (program : Program) (available : List DeclarationId) (calls : ClosureRuns available)
    {globals : List String} {state : State} {source : SourceExpr} {code : ResolvedExpr} {out : Outcome Value}
    (related : Operand globals source code) (evaluated : Evaluates state source out) :
    EvaluatesWith program available calls (fun _ => True) state code out := by
  induction evaluated generalizing code with
  | name name => cases related; exact .atom trivial .read
  | int n => cases related; exact .atom trivial .scalar
  | string s => cases related; exact .atom trivial .string
  | index _ _ recv sub =>
    cases related with
    | index receiver index => exact .index (recv receiver) (sub index)
  | receiverError _ recv =>
    cases related with
    | index receiver _ => exact .indexReceiverError (recv receiver)

theorem evaluates_operands (program : Program) (available : List DeclarationId) (calls : ClosureRuns available)
    {globals : List String} {state : State} {source : List SourceExpr} {codes : List ResolvedExpr}
    {out : Outcome (List Value)} (related : InOrder (Operand globals) source codes)
    (evaluated : EvaluatesOperands state source out) :
    EvaluatesManyWith program available calls (fun _ => True) state codes out := by
  induction evaluated generalizing codes with
  | nil => cases related; exact .empty
  | @cons firstSource rest value restOutcome first _ ih =>
    cases related with
    | cons head tail =>
      have headRun := evaluates_operand program available calls head first
      cases restOutcome with
      | ok values next => exact .cons headRun (ih tail)
      | error error next => exact .tailError headRun (ih tail)
  | error first =>
    cases related with
    | cons head _ => exact .headError (evaluates_operand program available calls head first)

open Silmaril.Languages.Starlark.Lists in
private def residual {α : Type} (outcome : Outcome α) : State :=
  match outcome with
  | .ok _ state | .error _ state => state

open Silmaril.Languages.Starlark.Lists in
private def Fixed {α : Type} (meaning : Meaning α) : Prop := ∀ state, residual (meaning state) = state

open Silmaril.Languages.Starlark.Lists in
private theorem fixed_bind {α β : Type} {operation : Meaning α} {thenRun : α → Meaning β}
    (first : Fixed operation) (last : ∀ result, Fixed (thenRun result)) : Fixed (operation >>= thenRun) := by
  intro state
  have before := first state
  cases executed : operation state with
  | ok value next =>
    have unchanged : next = state := by simpa [executed, residual] using before
    simpa [bind, EStateM.bind, executed, unchanged] using last value state
  | error error next =>
    simpa [bind, EStateM.bind, executed, residual] using before

open Silmaril.Languages.Starlark.Lists in
private theorem fixed_from_except {α : Type} (value : Except Silmaril.Languages.Starlark.Lists.Error α) : Fixed (fromExcept value) := by
  intro state
  cases value <;> rfl

open Silmaril.Languages.Starlark.Lists in
private theorem fixed_project {α : Type} (address : Address) (projection : Contents → Option α) :
    Fixed (projectCell address projection) := by
  apply fixed_bind (operation := getCell address)
  · intro state
    unfold getCell
    split <;> rfl
  · intro cell state
    cases projection cell.contents <;> rfl

open Silmaril.Languages.Starlark.Lists in
private theorem fixed_read_index (receiver index : Value) : Fixed (readIndex receiver index) := by
  cases receiver with
  | scalar | function | builtin => intro state; rfl
  | string | range => exact fixed_from_except _
  | list | tuple =>
    apply fixed_bind (fixed_project _ _)
    intro elements
    apply fixed_bind (fixed_from_except _)
    intro offset state
    rfl
  | dict address =>
    apply fixed_bind (operation := dictEntries address) (fixed_project _ _)
    intro entries state
    dsimp only
    split
    · rfl
    · split <;> rfl

theorem read_index_state (receiver index : Value) (state : State) :
    Silmaril.Languages.Starlark.Lists.Iteration.finishState (Silmaril.Languages.Starlark.Lists.readIndex receiver index state) = state :=
  fixed_read_index receiver index state

theorem operand_total {globals : List String} {source : SourceExpr} {code : ResolvedExpr}
    (related : Operand globals source code) (state : State) :
    ∃ out, Evaluates state source out ∧ Silmaril.Languages.Starlark.Lists.Iteration.finishState out = state := by
  induction related with
  | @global name _ _ =>
    exact ⟨_, .name name, by cases read : state.bindingValue (globalSlot name) <;> simp [State.read, read, Silmaril.Languages.Starlark.Lists.Iteration.finishState]⟩
  | int n => exact ⟨_, .int n, rfl⟩
  | string text => exact ⟨_, .string text, rfl⟩
  | index _ _ recv sub =>
    obtain ⟨out, first, same⟩ := recv
    cases out with
    | error error next =>
      change next = state at same
      subst next
      exact ⟨_, .receiverError first, rfl⟩
    | ok value next =>
      change next = state at same
      subst next
      obtain ⟨out, last, same⟩ := sub
      cases out with
      | error error next => exact ⟨_, .index first last, same⟩
      | ok key next =>
        change next = state at same
        subst next
        exact ⟨_, .index first last, fixed_read_index value key state⟩

theorem operands_total {globals : List String} {source : List SourceExpr} {resolved : List ResolvedExpr}
    (related : InOrder (Operand globals) source resolved) (state : State) :
    (∃ values, EvaluatesOperands state source (.ok values state)) ∨
      ∃ error, EvaluatesOperands state source (.error error state) := by
  induction related with
  | nil => exact .inl ⟨[], .nil⟩
  | cons head _ ih =>
    obtain ⟨out, first, same⟩ := operand_total head state
    cases out with
    | error error next =>
      change next = state at same
      subst next
      exact .inr ⟨error, .error first⟩
    | ok value next =>
      change next = state at same
      subst next
      rcases ih with ⟨values, last⟩ | ⟨error, last⟩
      · exact .inl ⟨value :: values, .cons first last⟩
      · exact .inr ⟨error, .cons first last⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall
