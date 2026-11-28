module

import Silmaril.Languages.Starlark.Functions.Thms
import Silmaril.Languages.Starlark.Lists.Thms
meta import Silmaril.Languages.Starlark.Functions.Builtins.Defs
meta import Silmaril.Languages.Starlark.Functions.Defs
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs
meta import Silmaril.Languages.Starlark.Lists.Denotation.Defs
meta import Silmaril.Languages.Starlark.Lists.Freeze.Defs
meta import Silmaril.Languages.Starlark.Lists.Iteration.Defs

namespace Silmaril.Languages.Starlark.Functions.Builtins

open Lists (Builtin State Outcome Error)
open Lists.Iteration (Flow finishState)

deriving instance DecidableEq for Except

private def slot (name : String) : Binding := ⟨.local, name⟩
private def read (name : String) : Lists.Expr := .read (.bound (slot name))
private def number (n : Int) : Lists.Value := .scalar (.int n)
private def flag (b : Bool) : Lists.Value := .scalar (.bool b)
private def int (n : Int) : Lists.Expr := .scalar (.int n)
private def list (xs : List Lists.Expr) : Lists.Expr := .list (operandList xs)
private def dict (xs : List (Lists.Expr × Lists.Expr)) : Lists.Expr :=
  .dict (xs.foldl (fun entries (k, v) => .entry entries k v) .noEntries)
private def set (name : String) (value : Lists.Expr) : Body :=
  .total (.atomic (.assign (slot name) value))
private def call (target : String) (callee : Lists.Expr) (args : Arguments) : Body :=
  .call (some (slot target)) callee args
private def seq (body : List Body) : Body := body.foldr Body.seq (.total (.atomic .pass))
private def frame (slots : List String) : State := (slots.map slot).foldl State.allocateSlot {}
private def result {α : Type} : Outcome α → Except Error α
  | .ok a _ => .ok a
  | .error e _ => .error e

private def apply (id : Builtin) (args : Arguments) (state : State := {}) : Outcome Flow :=
  run #[] (call "out" (.builtin id) args) state

private def inspect (id : Builtin) (args : Arguments) : Except Error Lists.Value :=
  match apply id args with
  | .error error _ => .error error
  | .ok _ state => state.bindingValue (slot "out")

#guard
  Builtin.resolve "len" = some .len ∧ Builtin.resolve "sorted" = none ∧
  inspect .bool {} = .ok (.scalar (.bool false)) ∧
  inspect .bool { positional := [.builtin .len] } = .ok (.scalar (.bool true)) ∧
  inspect .bool { positional := [list []] } = .ok (.scalar (.bool false)) ∧
  inspect .bool { positional := [dict [(.string "a", int 0)]] } = .ok (.scalar (.bool true)) ∧
  inspect .len { positional := [.string "é😀"] } = .ok (number 6) ∧
  inspect .len { star := list [list [int 1, int 2]] } = .ok (number 2) ∧
  inspect .len { positional := [list [int 5]], starStar := dict [] } = .ok (number 1) ∧
  inspect .type { positional := [.scalar .none] } = .ok (.string "NoneType") ∧
  inspect .type { positional := [.builtin .len] } = .ok (.string "builtin_function_or_method")

-- A resolved local named len may be bound to another callable.
#guard
  let program : Program := #[⟨{ positional := [⟨slot "len", none⟩, ⟨slot "x", none⟩] },
     [slot "r"], [], .seq (call "r" (read "len") { positional := [read "x"] })
       (.total (.ret (read "r")))⟩]
  let out := run program (seq [.define (slot "f") 0, set "alias" (.builtin .type),
    call "out" (read "f") { positional := [read "alias", int 0] }]) (frame ["f", "alias", "out"])
  result out = .ok .next ∧ (finishState out).bindingValue (slot "out") = .ok (.string "int") ∧
  result (Lists.denote (.index (dict [(.builtin .len, int 1), (.builtin .type, int 2)])
    (read "alias")) (finishState out)) = .ok (number 2)

#guard
  let entries := dict [(.string "z", int 1), (.string "a", int 2)]
  let state := finishState (run #[] (seq [
    call "emptyList" (.builtin .list) {}, call "emptyTuple" (.builtin .tuple) {},
    call "keysList" (.builtin .list) { positional := [entries] },
    call "keysTuple" (.builtin .tuple) { positional := [entries] }]))
  (match ["emptyList", "emptyTuple", "keysList", "keysTuple"].map
      (fun n => state.bindingValue (slot n)) with
   | [.ok (.list a), .ok (.tuple b), .ok (.list c), .ok (.tuple d)] =>
     decide (result (Lists.listElements a state) = .ok [] ∧
       result (Lists.tupleElements b state) = .ok [] ∧
       result (Lists.listElements c state) = .ok [.string "z", .string "a"] ∧
       result (Lists.tupleElements d state) = .ok [.string "z", .string "a"])
   | _ => false) = true

-- Copying a frozen source under iteration allocates only a new outer cell.
#guard
  let start := finishState (run #[] (seq [set "inner" (list [int 1]),
    set "source" (list [read "inner"])]))
  (match start.bindingValue (slot "source"), start.bindingValue (slot "inner") with
   | .ok (.list outer), .ok (.list inner) =>
     let before := { start.freeze [.list outer] with iterators := [outer] }
     let out := apply .list { positional := [read "source"] } before
     let after := finishState out
     match after.bindingValue (slot "out") with
     | .ok (.list fresh) =>
       decide (result out = .ok .next ∧ fresh = before.heap.size ∧
         after.heap = before.heap.push ⟨.list [.list inner], false⟩ ∧
         after.iterators = [outer] ∧
         result (Lists.appendAt inner (number 2) after) = .error (.frozen inner))
     | _ => false
   | _, _ => false) = true

-- Range materialization preserves existing heap cells and active guards.
-- A tuple's internal cell carries the structural integer key.
#guard
  let original : State := { heap := #[⟨.list [], false⟩], iterators := [0] }
  let span : Lists.RangeValue := ⟨10^24 + 4, 10^24, -2, by decide⟩
  let before := original.write (slot "span") (.range span)
  let args : Arguments := { positional := [read "span"] }
  let values := [number (10^24 + 4), number (10^24 + 2)]
  let key : Lists.Key := [.openTuple, .scalar (.int (10^24 + 4)), .scalar (.int (10^24 + 2)), .closeTuple]
  let listState := finishState (apply .list args before)
  let tupleState := finishState (apply .tuple args before)
  listState.bindingValue (slot "out") = .ok (.list 1) ∧
    listState.heap = before.heap.push ⟨.list values, false⟩ ∧ listState.iterators = [0] ∧
    tupleState.bindingValue (slot "out") = .ok (.tuple 1) ∧
    tupleState.heap = before.heap.push ⟨.tuple values (some key), false⟩ ∧ tupleState.iterators = [0]

#guard
  inspect .len {} = .error (.builtinArity .len 1 1 0) ∧
  inspect .bool { positional := [int 1, int 2] } = .error (.builtinArity .bool 0 1 2) ∧
  inspect .type { positional := [int 1, int 2] } = .error (.builtinArity .type 1 1 2) ∧
  inspect .len { positional := [.scalar .none] } = .error (.builtinType .len (.scalar .none)) ∧
  inspect .list { positional := [.string "x"] } = .error (.builtinType .list (.string "x")) ∧
  inspect .tuple { positional := [.string "x"] } = .error (.builtinType .tuple (.string "x")) ∧
  inspect .type { starStar := dict [(.string "x", int 1)] } = .error (.builtinKeyword .type "x") ∧
  inspect .len { star := int 1, starStar := dict [(.string "x", int 1)] } = .error .invalidStar

-- All operands execute before rejection, and the failed call leaves its destination alone.
#guard
  let before := finishState (run #[] (seq [set "events" (list []), set "out" (int 9)]))
  let append := fun n => Lists.Code.append (read "events") (int n)
  let out := apply .len { positional := [append 1, append 2], keywords := [("ignored", append 3)] } before
  let after := finishState out
  result out = .error (.builtinKeyword .len "ignored") ∧
  after.bindingValue (slot "out") = .ok (number 9) ∧
  after.heap = #[⟨.list ([1, 2, 3].map number), false⟩]

#guard
  Builtin.resolve "abs" = some .abs ∧ Builtin.resolve "any" = some .any ∧
  Builtin.resolve "all" = some .all ∧
  inspect .abs { positional := [int (-(10^30))] } = .ok (number (10^30)) ∧
  inspect .abs { positional := [int 0] } = .ok (number 0) ∧
  inspect .abs { positional := [int 7] } = .ok (number 7) ∧
  inspect .any { positional := [list []] } = .ok (flag false) ∧
  inspect .all { positional := [.tuple .empty] } = .ok (flag true) ∧
  inspect .any { positional := [list [int 0, .scalar .none, list [], .string "x"]] } = .ok (flag true) ∧
  inspect .all { positional := [.tuple (operandList [int 1, list [], int 2])] } = .ok (flag false) ∧
  inspect .any { positional := [dict [(int 0, .scalar (.bool true))]] } = .ok (flag false) ∧
  inspect .all { positional := [dict [(.string "x", .scalar (.bool false))]] } = .ok (flag true) ∧
  inspect .any { star := list [list [int 0, .builtin .abs]], starStar := dict [] } = .ok (flag true)

-- Calling a new builtin through a local alias uses the same first-class key.
#guard
  let out := run #[] (seq [set "alias" (.builtin .abs),
    call "out" (read "alias") { positional := [int (-7)] }])
  let after := finishState out
  result out = .ok .next ∧ after.bindingValue (slot "out") = .ok (number 7) ∧
    result (Lists.denote (.index (dict [(.builtin .abs, int 1), (.builtin .any, int 2)])
      (read "alias")) after) = .ok (number 1)

-- The long range reaches a decision after at most two yields and allocates nothing.
#guard
  let before : State := { iterators := [3] }
  let empty : Lists.RangeValue := ⟨0, 0, 1, by decide⟩
  let large : Lists.RangeValue := ⟨0, 10^30, 1, by decide⟩
  let descending : Lists.RangeValue := ⟨5, 1, -2, by decide⟩
  let runRange := fun id span => apply id { positional := [read "span"] }
    (before.write (slot "span") (.range span))
  let checks : List (Builtin × Lists.RangeValue × Bool) :=
    [(.any, empty, false), (.all, empty, true), (.any, large, true), (.all, large, false),
      (.all, descending, true)]
  checks.all (fun (id, span, expected) =>
    let out := runRange id span
    let after := finishState out
    decide (result out = .ok .next ∧ after.bindingValue (slot "out") = .ok (flag expected) ∧
      after.heap = before.heap ∧ after.iterators = before.iterators)) = true

-- Malformed resolved stores distinguish the skipped tail, first truth error and acquisition error.
#guard
  let before : State := { heap := #[⟨.list [number 0, .list 5, .tuple 0], true⟩,
    ⟨.list [number 1, .list 5], false⟩, ⟨.list [number 0, .tuple 0], false⟩], iterators := [0] }
  let runList := fun id addr => invoke id ⟨[.list addr], []⟩ before
  let skippedFalse := runList .all 0
  let skippedTrue := runList .any 1
  let failed := runList .any 0
  result skippedFalse = .ok (flag false) ∧ result skippedTrue = .ok (flag true) ∧
    result failed = .error (.danglingAddress 5) ∧ result (runList .all 1) = .error (.danglingAddress 5) ∧
    result (runList .any 2) = .error (.wrongCellKind 0) ∧
    result (runList .all 9) = .error (.danglingAddress 9) ∧
    (finishState failed).heap = before.heap ∧ (finishState failed).iterators = before.iterators

#guard
  inspect .abs {} = .error (.builtinArity .abs 1 1 0) ∧
  inspect .any {} = .error (.builtinArity .any 1 1 0) ∧
  inspect .all {} = .error (.builtinArity .all 1 1 0) ∧
  inspect .abs { positional := [.scalar (.bool true)] } = .error (.builtinType .abs (flag true)) ∧
  inspect .any { positional := [.scalar .none] } = .error (.builtinType .any (.scalar .none)) ∧
  inspect .all { positional := [.string "x"] } = .error (.builtinType .all (.string "x"))

-- Checked expression operands retain the exact reached effects and leave a failed destination alone.
#guard
  let before := finishState (run #[] (seq [set "events" (list []), set "out" (int 99)]))
  let note := fun n (value : Lowering.Expr) =>
    Lowering.Expr.branch (.atom (.append (read "events") (int n))) value value
  let zero := Lowering.Expr.atom (int 0)
  let someTrue := Lowering.Expr.atom (.builtin .any)
  let every := Lowering.Expr.atom (.builtin .all)
  let lenError := Lowering.Expr.callPos (.atom (.builtin .len)) [note 2 zero]
  let calls : List (Lowering.Expr × Error × List Int) := [
    (.call (note 1 someTrue) [note 2 zero, note 3 zero] [("ignored", note 4 zero)] none none,
      .builtinKeyword .any "ignored", [1, 2, 3, 4]),
    (.callPos every [note 1 zero, note 2 (.list [])], .builtinArity .all 1 1 2, [1, 2]),
    (.call someTrue [] [] (some (note 1 zero)) (some (note 2 (.dict [(.atom (.string "x"), zero)]))),
      .invalidStar, [1, 2]),
    (.call every [note 1 zero, lenError] [("ignored", note 3 zero)] none none,
      .builtinType .len (number 0), [1, 2])]
  calls.all (fun (expr, error, events) =>
    let out := run #[] (.assignExpr (slot "out") expr) before
    let after := finishState out
    decide (result out = .error error ∧ after.bindingValue (slot "out") = .ok (number 99) ∧
      result (Lists.listElements 0 after) = .ok (events.map number) ∧
      after.iterators = before.iterators)) = true

end Silmaril.Languages.Starlark.Functions.Builtins
