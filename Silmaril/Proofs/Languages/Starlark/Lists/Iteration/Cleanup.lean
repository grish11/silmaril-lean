module

public import Silmaril.Languages.Starlark.Lists.Iteration.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.Iteration

open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration

private def Preserves {α : Type} (action : Meaning α) : Prop :=
  ∀ state, (finishState (action state)).iterators = state.iterators

private theorem resume_preserves {α β : Type} (out : Outcome α) (action : α → Meaning β)
    (h : ∀ value, Preserves (action value)) :
    (finishState (Outcome.resume out action)).iterators = (finishState out).iterators := by
  cases out
  next value state => exact h value state
  next => rfl

private theorem keeps_pure {α : Type} (a : α) : Preserves (pure a) :=
  fun _ => rfl

private theorem keeps_throw {α : Type} (e : Error) : Preserves (throw e : Meaning α) :=
  fun _ => rfl

private theorem keeps_bind {α β : Type} {first : Meaning α} {rest : α → Meaning β}
    (hFirst : Preserves first) (hRest : ∀ value, Preserves (rest value)) :
    Preserves (first >>= rest) := by
  intro state
  have h := hFirst state
  cases result : first state with
  | ok value next =>
    simpa [bind, EStateM.bind, result] using (hRest value next).trans (by simpa [result, finishState] using h)
  | error error next =>
    simpa [bind, EStateM.bind, result, finishState] using h

private theorem keeps_map {α β : Type} (f : α → β) {action : Meaning α} (h : Preserves action) :
    Preserves (f <$> action) := by
  intro state
  have unchanged := h state
  cases hx : action state <;>
    simpa [Functor.map, EStateM.map, hx, finishState] using unchanged

private theorem keeps_getCell (address : Address) : Preserves (getCell address) := by
  intro state
  unfold getCell
  split <;> rfl

private theorem keeps_except {α : Type} (out : Except Error α) : Preserves (fromExcept out) := by
  cases out <;> (intro state; rfl)

private theorem keeps_project {α : Type} (address : Address) (project : Contents → Option α) :
    Preserves (projectCell address project) := by
  unfold projectCell
  apply keeps_bind (keeps_getCell address)
  intro cell
  cases project cell.contents
  · exact keeps_throw _
  · exact keeps_pure _

private theorem keeps_edit (address : Address) (edit : Contents → Except Error Contents) :
    Preserves (editCell address edit) := by
  unfold editCell
  apply keeps_bind (keeps_getCell _)
  intro cell state
  split
  · rfl
  · dsimp only
    split
    · rfl
    · split
      · rfl
      · split <;> rfl

private theorem keeps_update (address : Address) (edit : List Value → Except Error (List Value)) :
    Preserves (updateCell address edit) := by
  unfold updateCell
  exact keeps_bind (keeps_project _ _) fun _ =>
    keeps_bind (keeps_except _) fun _ => keeps_edit _ _

private theorem keeps_readSequence (elements : List Value) (index : Value) :
    Preserves (readSequence elements index) := by
  unfold readSequence
  exact keeps_bind (keeps_except _) fun _ => keeps_pure _

private theorem keeps_readIndex (receiver index : Value) : Preserves (readIndex receiver index) := by
  cases receiver with
  | scalar | function | builtin | string => exact keeps_throw _
  | list =>
    rw [readIndex]
    exact keeps_bind (keeps_project _ _) (keeps_readSequence · index)
  | tuple =>
    rw [readIndex]
    exact keeps_bind (keeps_project _ _) (keeps_readSequence · index)
  | dict address =>
    rw [readIndex, readDict]
    apply keeps_bind (keeps_project _ _)
    intro entries state
    dsimp only
    split
    · rfl
    · split <;> rfl

private theorem keeps_writeIndex (receiver index value : Value) :
    Preserves (writeIndex receiver index value) := by
  cases receiver with
  | scalar | tuple | function | builtin | string => exact keeps_throw _
  | list =>
    rw [writeIndex]
    exact keeps_update _ _
  | dict =>
    rw [writeIndex]
    intro state
    unfold writeDict
    exact keeps_edit _ _ state

private theorem keeps_append (address : Address) (value : Value) :
    Preserves (appendAt address value) := by
  unfold appendAt
  exact keeps_bind (keeps_update _ _) fun _ => keeps_pure _

private theorem keeps_displayEntry (entries : List Entry) (key value : Value) :
    Preserves (addDisplayEntry entries key value) := by
  intro state
  unfold addDisplayEntry
  split
  · rfl
  · split <;> rfl

private theorem keeps_code {α : Type} (code : Code α) : Preserves (denote code) := by
  induction code with
  | scalar | builtin | string => exact keeps_pure _
  | read ref =>
    intro state
    cases ref with
    | predeclared => rfl
    | bound =>
      simp only [denote, State.read]
      split <;> rfl
  | list elements ih =>
    rw [denote]
    exact keeps_bind ih fun _ _ => rfl
  | tuple elements ih =>
    rw [denote]
    exact keeps_bind ih fun _ _ => rfl
  | dict entries ih =>
    rw [denote]
    exact keeps_bind ih fun _ _ => rfl
  | noEntries => exact keeps_pure _
  | entry earlier key value ihPrefix ihKey ihValue =>
    rw [denote]
    exact keeps_bind ihPrefix fun entries => keeps_bind ihKey fun k =>
      keeps_bind ihValue (keeps_displayEntry entries k)
  | empty => exact keeps_pure _
  | cons head tail ihHead ihTail =>
    rw [denote]
    exact keeps_bind ihHead fun _ => keeps_map _ ihTail
  | index receiver index ihReceiver ihIndex =>
    rw [denote]
    exact keeps_bind ihReceiver fun value => keeps_bind ihIndex (keeps_readIndex value)
  | append receiver argument ihReceiver ihArgument =>
    rw [denote]
    apply keeps_bind ihReceiver
    intro value
    cases value with
    | scalar | tuple | dict | function | builtin | string => exact keeps_throw _
    | list address => exact keeps_bind ihArgument (keeps_append address)
  | pass => exact keeps_pure _
  | eval expr ih =>
    rw [denote]
    exact keeps_bind ih fun _ => keeps_pure _
  | assign binding rhs ih =>
    rw [denote]
    apply keeps_bind ih
    intro value state
    simp only [bindValue, finishState, State.write]
    split
    · rfl
    · rfl
    · split <;> rfl
  | setIndex receiver index rhs ihReceiver ihIndex ihRhs =>
    rw [denote]
    exact keeps_bind ihRhs fun value => keeps_bind ihReceiver fun dst =>
      keeps_bind ihIndex fun i => keeps_writeIndex dst i value
  | seq first rest ihFirst ihRest =>
    rw [denote]
    exact keeps_bind ihFirst fun _ => ihRest

private theorem keeps_truth (value : Value) : Preserves (truth value) := by
  cases value with
  | scalar | function | builtin | string => exact keeps_pure _
  | list | tuple | dict =>
    rw [truth]
    exact keeps_map _ (keeps_project _ _)

private theorem keeps_source (value : Value) : Preserves (iterationSource value) := by
  cases value with
  | scalar | function | builtin | string => exact keeps_throw _
  | list | tuple | dict =>
    rw [iterationSource]
    exact keeps_map _ (keeps_project _ _)

private theorem restore_stack (stack : List Address) (out : Outcome Flow) :
    (finishState (restoreIterators stack out)).iterators = stack := by
  cases out <;> rfl

theorem iterators_denoteSuite {depth : Nat} (code : Suite depth) (state : State) :
    (finishState (denoteSuite code state)).iterators = state.iterators := by
  induction code generalizing state with
  | atomic stmt =>
    rw [denoteSuite, resume_preserves _ _ (fun _ => keeps_pure _)]
    exact keeps_code stmt state
  | seq first rest ihFirst ihRest =>
    rw [denoteSuite]
    refine (resume_preserves _ _ ?_).trans (ihFirst state)
    intro signal
    cases signal
    · exact ihRest
    all_goals exact keeps_pure _
  | branch test yes no ihYes ihNo =>
    rw [denoteSuite, resume_preserves, resume_preserves _ _ keeps_truth]
    · exact keeps_code test state
    · intro flag
      cases flag
      · exact ihNo
      · exact ihYes
  | forIn target iterable body _ =>
    rw [denoteSuite]
    refine (resume_preserves (Outcome.resume (denote iterable state) iterationSource) _ ?_).trans
      ((resume_preserves _ _ keeps_source).trans (keeps_code iterable state))
    intro pair next
    obtain ⟨address, elements⟩ := pair
    exact restore_stack _ _
  | breakLoop => rfl
  | continueLoop => rfl
  | ret value =>
    rw [denoteSuite, resume_preserves _ _ (fun _ => keeps_pure _)]
    exact keeps_code value state

theorem editCell_iterating (state : State) (address : Address)
    (edit : Contents → Except Error Contents) {cell : Cell}
    (found : state.heap[address]? = some cell) (mutable : cell.frozen = false)
    (active : address ∈ state.iterators) :
    editCell address edit state = .error (.activeIteration address) state := by
  simp [editCell, getCell, bind, EStateM.bind, found, mutable, active]

end Silmaril.Proofs.Languages.Starlark.Lists.Iteration
