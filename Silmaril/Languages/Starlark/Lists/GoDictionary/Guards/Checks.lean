module

import Silmaril.Languages.Starlark.Lists.GoDictionary.Guards.Thms
meta import Silmaril.Languages.Starlark.Lists.GoDictionary.Guards.Defs
meta import Silmaril.Languages.Starlark.Lists.Iteration.Defs

namespace Silmaril.Languages.Starlark.Lists.GoDictionary.Guards

deriving instance DecidableEq for Except

private def badKey : Value := .list 42
private def item : Value := .scalar (.int 7)
private def snapshot (table : Table) : Bool × Nat × Bool × List Value :=
  (table.frozen, table.activeIterators, table.contents.isSome, table.rows.keys)

private def physical {α : Type} (out : MutationOutcome α) :
    Except MutationError α × (Bool × Nat × Bool × List Value) :=
  match out with
  | .ok value after => (.ok value, snapshot after)
  | .error error after => (.error error, snapshot after)

private def canonical (out : Outcome Unit) : Except Lists.Error Unit × Heap × List Lists.Address :=
  match out with
  | .ok () after => (.ok (), after.heap, after.iterators)
  | .error error after => (.error error, after.heap, after.iterators)

-- The key would be rejected if hashing were reached. Freeze wins when both
-- guards apply. The display helper validates its pair before the cell edit.
#guard
  let table : Table := { contents := some Deletion.Table.empty, frozen := true, activeIterators := 1 }
  let state : State := { heap := #[⟨.dict [], true⟩], iterators := [0] }
  let active : Table := { table with frozen := false }
  let iterating : State := { state with heap := #[⟨.dict [], false⟩] }
  decide (physical (Guards.set state.heap table badKey item) = (.error (.guard .frozen), snapshot table)) &&
    decide (physical (Guards.delete state.heap table badKey) =
      (.error (.guard .frozen), snapshot table)) &&
    decide (canonical (writeDict 0 badKey item state) = (.error (.frozen 0), state.heap, [0])) &&
    decide (physical (Guards.set iterating.heap active badKey item) =
      (.error (.guard .activeIteration), snapshot active)) &&
    decide (physical (Guards.delete iterating.heap active badKey) =
      (.error (.guard .activeIteration), snapshot active)) &&
    decide (canonical (writeDict 0 badKey item iterating) =
      (.error (.activeIteration 0), iterating.heap, [0])) &&
    decide (canonical (insertDisplayEntry (.dict 0) badKey item state) =
      (.error (.unhashableKey badKey), state.heap, [0]))

-- Active guards also apply to unallocated tables. Once a live assignment
-- reaches hashing, even a hash failure leaves an initialized empty table.
#guard
  let zero : Table := {}
  let state : State := { heap := #[⟨.dict [], false⟩] }
  let active := zero.enterIterator
  let vetoed := Iteration.pushIterator state 0
  let frozen : Table := { frozen := true }
  let frozenState : State := { heap := #[⟨.dict [], true⟩] }
  decide (physical (Guards.delete state.heap zero badKey) = (.ok (none : Option Value), snapshot zero)) &&
    decide (physical (Guards.set vetoed.heap active badKey item) =
      (.error (.guard .activeIteration), snapshot active)) &&
    decide (canonical (writeDict 0 badKey item vetoed) = (.error (.activeIteration 0), vetoed.heap, [0])) &&
    decide (physical (Guards.delete state.heap frozen badKey) = (.error (.guard .frozen), snapshot frozen)) &&
    decide (frozen.enterIterator.activeIterators = 0) &&
    decide (canonical (writeDict 0 badKey item (Iteration.pushIterator frozenState 0)) =
      (.error (.frozen 0), frozenState.heap, [0])) &&
    decide (canonical (writeDict 0 badKey item state) = (.error (.unhashableKey badKey), state.heap, [])) &&
    (match Guards.set state.heap zero badKey item with
    | .ok .. => false
    | .error error after =>
      decide (error = .table (.unsupportedKey badKey) ∧ snapshot after = (false, 0, true, []) ∧
        physical (Guards.delete state.heap after badKey) = (.error (.table (.unsupportedKey badKey)), snapshot after)))

#guard
  let zero : Table := {}
  let state : State := { heap := #[⟨.dict [], false⟩] }
  let key : Value := .scalar (.int 0)
  let alias : Value := .scalar (.float 0x8000000000000000)
  match Guards.set state.heap zero key item, writeDict 0 key item state with
  | .ok () table, .ok () after =>
    let guarded := table.enterIterator
    let iterating := Iteration.pushIterator after 0
    decide (table.contents.isSome = true ∧
      physical (Guards.set after.heap table alias (.scalar .none)) = (.ok (), (false, 0, true, [key])) ∧
      physical (Guards.delete after.heap table alias) = (.ok (some item), (false, 0, true, []))) &&
      (match writeDict 0 alias (.scalar .none) after with
      | .ok () final => decide (final.heap[0]? = some ⟨.dict [⟨key, [.scalar (.int 0)], .scalar .none⟩], false⟩)
      | .error .. => false) &&
    decide (physical (Guards.set iterating.heap guarded alias (.scalar .none)) =
      (.error (.guard .activeIteration), snapshot guarded)) &&
    decide (canonical (writeDict 0 alias (.scalar .none) iterating) =
      (.error (.activeIteration 0), iterating.heap, [0]))
  | _, _ => false

-- Right-hand and key allocation effects precede the write guard. A source
-- error from either operand keeps exactly the heap reached at that phase.
#guard
  let receiver : Binding := ⟨.local, "d"⟩
  let missing : Binding := ⟨.local, "missing"⟩
  let listExpr : Expr := .list .empty
  let state : State := { heap := #[⟨.dict [], true⟩], bindings := fun b =>
    if b = receiver then some (.dict 0) else none }
  decide (canonical (denote (.setIndex (.read (.bound receiver)) listExpr listExpr) state) =
    (.error (.frozen 0), #[⟨.dict [], true⟩, ⟨.list [], false⟩, ⟨.list [], false⟩], []) ∧
    canonical (denote (.setIndex (.read (.bound receiver)) (.read (.bound missing)) listExpr) state) =
      (.error (.uninitialized missing), #[⟨.dict [], true⟩, ⟨.list [], false⟩], []) ∧
    canonical (denote (.setIndex (.read (.bound missing)) listExpr listExpr) state) =
      (.error (.uninitialized missing), #[⟨.dict [], true⟩, ⟨.list [], false⟩], []) ∧
    canonical (writeDict 42 badKey item state) = (.error (.danglingAddress 42), state.heap, []))

end Silmaril.Languages.Starlark.Lists.GoDictionary.Guards
