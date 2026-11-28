module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Guards.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Guards.Agreement

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Guards

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Lists (State Entry Expr denote writeDict writeIndex)
open Silmaril.Languages.Starlark.Lists.GoDictionary.Guards

private theorem bind_resume {α β : Type}
    (first : Lists.Meaning α) (second : α → Lists.Meaning β) (state : State) :
    (first >>= second) state = Lists.Outcome.resume (first state) second := by
  cases ran : first state <;> simp [bind, EStateM.bind, Lists.Outcome.resume, ran]

theorem denote_setIndex (state : State) (receiver index rhs : Expr) :
    denote (.setIndex receiver index rhs) state =
      Lists.Outcome.resume (denote rhs state) (fun value afterRhs =>
        Lists.Outcome.resume (denote receiver afterRhs) (fun target afterReceiver =>
          Lists.Outcome.resume (denote index afterReceiver) (fun key => writeIndex target key value))) := by
  simp only [denote, bind_resume]
  apply congrArg (Lists.Outcome.resume (denote rhs state))
  funext value afterRhs
  rw [bind_resume]
  apply congrArg (Lists.Outcome.resume (denote receiver afterRhs))
  funext target afterReceiver
  rw [bind_resume]

theorem setIndex_uninitialized (state afterRhs : State) (binding : Binding)
    (index rhs : Expr) (value : Lists.Value)
    (right : denote rhs state = .ok value afterRhs)
    (missing : afterRhs.bindingValue binding = .error (.uninitialized binding)) :
    denote (.setIndex (.read (.bound binding)) index rhs) state =
      .error (.uninitialized binding) afterRhs := by
  rw [denote_setIndex, right]
  simp [Lists.Outcome.resume, denote, Lists.State.read, missing]

theorem setIndex_key_error (state afterRhs afterReceiver afterKey : State)
    (receiver index rhs : Expr) (target value : Lists.Value) (error : Lists.Error)
    (right : denote rhs state = .ok value afterRhs)
    (readReceiver : denote receiver afterRhs = .ok target afterReceiver)
    (readKey : denote index afterReceiver = .error error afterKey) :
    denote (.setIndex receiver index rhs) state = .error error afterKey := by
  simp [denote_setIndex, Lists.Outcome.resume, right, readReceiver, readKey]

theorem setIndex_lockstep (state afterRhs afterReceiver afterKey : State) (address : Lists.Address)
    (table : Table) (entries : List Entry) (receiver index rhs : Expr) (key value : Lists.Value)
    (right : denote rhs state = .ok value afterRhs)
    (readReceiver : denote receiver afterRhs = .ok (.dict address) afterReceiver)
    (readKey : denote index afterReceiver = .ok key afterKey)
    (related : Related afterKey address table entries)
    (domain : (∃ scalar, key = .scalar scalar) ∨ Unhashable key) :
    AssignsTogether afterKey address table entries
      (Lists.GoDictionary.Guards.set afterKey.heap table key value)
      (denote (.setIndex receiver index rhs) state) := by
  simpa only [denote_setIndex, right, Lists.Outcome.resume, readReceiver, readKey, writeIndex] using
    writeDict_lockstep afterKey address table entries key value related domain

/-- The display helper checks the key before attempting the cell edit. -/
theorem display_unhashable (state : State) (address : Lists.Address) (entries : List Entry)
    (frozen : Bool) (key value : Lists.Value)
    (cell : state.heap[address]? = some ⟨.dict entries, frozen⟩) (shape : Unhashable key) :
    Lists.insertDisplayEntry (.dict address) key value state = .error (.unhashableKey key) state := by
  have encoded : state.keyOf key = .error (.unhashableKey key) := by
    cases shape <;> rfl
  simp [Lists.insertDisplayEntry, Lists.addDisplayEntry, Lists.dictEntries, Lists.projectCell,
    Lists.getCell, bind, EStateM.bind, pure, EStateM.pure, encoded, cell]

end Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Guards
