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

end Silmaril.Languages.Starlark.Functions.Builtins
