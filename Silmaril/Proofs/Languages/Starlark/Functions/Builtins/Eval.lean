module

public import Silmaril.Languages.Starlark.Functions.Builtins.Operational.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Builtins

open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Builtins
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration (iterationSource truth)

private theorem runBind {α β : Type} (first : Meaning α) (next : α → Meaning β)
    (state : State) : (first >>= next) state = Outcome.resume (first state) next := by
  cases h : first state <;> simp [bind, EStateM.bind, Outcome.resume, h]

private theorem runMap {α β : Type} (f : α → β) (first : Meaning α) (state : State) :
    (f <$> first) state = Outcome.resume (first state) (fun value => pure (f value)) := by
  cases h : first state <;> simp [Functor.map, EStateM.map, Outcome.resume, h] <;> rfl

private theorem items_eq_of_reads {id : Builtin} {state : State}
    {value : Value} {out : Outcome (List Value)} (h : Items id state value out) :
    items id value state = out := by
  cases h with
  | list address =>
    simp only [items, iterationSource, runMap]
    cases listElements address state <;> rfl
  | tuple address =>
    simp only [items, iterationSource, runMap]
    cases tupleElements address state <;> rfl
  | dict address =>
    simp only [items, iterationSource, runMap]
    cases dictEntries address state <;> rfl
  | invalid h =>
    cases value <;> simp_all [IsCollection] <;> rfl

private theorem reads_items (id : Builtin) (state : State) (value : Value) :
    Items id state value (items id value state) := by
  cases value with
  | list address => exact items_eq_of_reads (.list address) ▸ Items.list address
  | tuple address => exact items_eq_of_reads (.tuple address) ▸ Items.tuple address
  | dict address => exact items_eq_of_reads (.dict address) ▸ Items.dict address
  | scalar | string | builtin | function => exact .invalid (by simp [IsCollection])

theorem invoke_eq_of_invokes {state : State} {id : Builtin} {args : Actual} {out : Outcome Value}
    (h : Invokes state id args out) : invoke id args state = out := by
  cases h with
  | missing h => cases id <;> simp_all [minArity] <;> rfl
  | bool => exact runMap _ _ _
  | @lenCollection value out noString reads =>
    have read := items_eq_of_reads reads
    cases value <;> simp_all [invoke, unary, runMap]
  | list reads => simp only [invoke, unary, runBind, items_eq_of_reads reads]
  | tuple reads => simp only [invoke, unary, runBind, items_eq_of_reads reads]
  | _ => rfl

theorem invokes_invoke (state : State) (id : Builtin) (args : Actual) :
    Invokes state id args (invoke id args state) := by
  obtain ⟨positional, keywords⟩ := args
  cases keywords with
  | cons entry rest => cases entry; exact .keyword
  | nil =>
    cases positional with
    | nil =>
      cases id
      · exact .emptyBool
      · exact .missing rfl
      · exact .missing rfl
      · exact .emptyList
      · exact .emptyTuple
    | cons value tail =>
      cases tail with
      | cons => exact .extra
      | nil =>
        cases id with
        | bool => simpa only [invoke, unary, runMap] using Invokes.bool (state := state) (value := value)
        | type => exact .type
        | list => simpa only [invoke, unary, runBind] using Invokes.list (reads_items .list state value)
        | tuple => simpa only [invoke, unary, runBind] using Invokes.tuple (reads_items .tuple state value)
        | len =>
          cases value with
          | string => exact .lenString
          | scalar | list | tuple | dict | function | builtin =>
            simp only [invoke, unary, runMap]
            exact .lenCollection (by intro _ equality; cases equality) (reads_items .len state _)

end Silmaril.Proofs.Languages.Starlark.Functions.Builtins
