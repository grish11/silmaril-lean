module

import Silmaril.Languages.Starlark.Lists.Iteration.Thms
import Silmaril.Languages.Starlark.Lists.Thms

namespace Silmaril.Languages.Starlark.Lists

open Iteration (Suite denoteSuite finishState)

deriving instance DecidableEq for Except

private def localSlot (name : String) : Binding := ⟨.local, name⟩
private def read (name : String) : Expr := .read (.bound (localSlot name))
private def int (n : Int) : Expr := .scalar (.int n)
private def bool (b : Bool) : Expr := .scalar (.bool b)
private def spine (values : List Expr) : Code (List Value) := values.foldr Code.cons .empty
private def list (values : List Expr) : Expr := .list (spine values)
private def tuple (values : List Expr) : Expr := .tuple (spine values)
private def dict (entries : List (Expr × Expr)) : Expr :=
  .dict (entries.foldl (fun earlier entry => .entry earlier entry.1 entry.2) .noEntries)
private def assign (name : String) (rhs : Expr) : Stmt := .assign (localSlot name) rhs
private def suite (stmts : List Stmt) : Stmt := stmts.foldr Code.seq .pass
private def append (name : String) (value : Expr) : Expr := .append (read name) value
private def result {α : Type} : Outcome α → Except Error α
  | .ok a _ => .ok a
  | .error e _ => .error e
private def run {α : Type} (setup : Stmt) (action : Meaning α) : Outcome α :=
  Outcome.resume (denote setup {}) fun () => action
private def frozen (state : State) (name : String) : State :=
  state.freeze ((state.bindings (localSlot name)).toList)

private def nestedKey : Expr :=
  tuple [tuple [], tuple [bool true, int 1], .scalar .none]

private def keyProgram : Stmt := suite
  [assign "key" nestedKey, assign "d" (dict
    [(tuple [bool true], int 10), (tuple [int 1], int 20), (read "key", int 30)]),
   assign "alias" (read "d"),
   .setIndex (read "alias") nestedKey (int 42),
   assign "hit" (.index (read "d") (read "key")),
   assign "trueKey" (.index (read "d") (tuple [bool true])),
   assign "intKey" (.index (read "d") (tuple [int 1]))]

-- Separately allocated but structurally equal tuple keys hit the original entry.
-- The Boolean and integer keys remain distinct.
example :
    let out := denote keyProgram {}
    let state := finishState out
    result out = .ok () ∧
    state.bindings (localSlot "hit") = some (.scalar (.int 42)) ∧
    state.bindings (localSlot "trueKey") = some (.scalar (.int 10)) ∧
    state.bindings (localSlot "intKey") = some (.scalar (.int 20)) ∧
    (match state.bindings (localSlot "d") with
     | some (.dict a) => (result (dictEntries a state)).toOption.map (List.map Entry.key)
     | _ => none) = some [.tuple 3, .tuple 4, .tuple 2] :=
  by decide +kernel

example :
    result (denote (.index (tuple [int 1, int 2]) (int (-1))) {}) = .ok (.scalar (.int 2)) ∧
    result (denote (.setIndex (tuple [int 1]) (int 0) (int 2)) {}) = .error .assignmentTarget ∧
    result (denote (.index (dict []) (int 2)) {}) = .error (.missingKey (.scalar (.int 2))) ∧
    result (denote (dict [(tuple [list []], int 0)]) {}) = .error (.unhashableKey (.tuple 1)) :=
  by decide +kernel

-- A duplicate is rejected after its own value runs and before a later pair.
example :
    let out := run (assign "a" (list [])) (denote (dict
      [(tuple [int 1], append "a" (int 1)), (tuple [int 1], append "a" (int 2)),
       (tuple [int 2], append "a" (int 3))]))
    result out = .error (.duplicateKey (.tuple 2)) ∧
    (finishState out).heap[0]? = some ⟨.list [.scalar (.int 1), .scalar (.int 2)], false⟩ :=
  by decide +kernel

private def cyclic : Stmt := suite
  [assign "leaf" (list []), assign "d" (dict []), assign "root" (tuple [read "d"]),
   .setIndex (read "d") (int 1) (read "leaf"), .eval (append "leaf" (read "root")),
   assign "spare" (list [])]

-- The tuple, mapping value and list form a cycle. Publication preserves reads.
example :
    let state := frozen (finishState (denote cyclic {})) "root"
    state.heap.toList.map Cell.frozen = [true, true, true, false] ∧
    result (denote (.index (.index (read "root") (int 0)) (int 1)) state) = .ok (.list 0) ∧
    result (denote (append "leaf" (int 2)) state) = .error (.frozen 0) ∧
    result (denote (.setIndex (read "d") (read "leaf") (int 2)) state) = .error (.frozen 1) ∧
    result (denote (append "spare" (int 2)) state) = .ok (.scalar .none) ∧
    result (denote (.index (read "d") (read "leaf")) state) = .error (.unhashableKey (.list 0)) ∧
    result (denote (.index (read "d") (read "d")) state) = .error (.unhashableKey (.dict 1)) :=
  by decide +kernel

private def sortedKeys : Stmt := suite
  [assign "d" (dict [(int 3, int 10), (int 1, int 20)]), assign "alias" (read "d"),
   .setIndex (read "alias") (int 3) (int 11), .setIndex (read "alias") (int 2) (int 12),
   assign "out" (list [])]

private def enumerateKeys : Suite 0 :=
  .seq (.forIn (localSlot "x") (tuple [int 8, int 9]) (.atomic (.eval (append "out" (read "x")))))
    (.forIn (localSlot "key") (read "d") (.atomic (.eval (append "out" (read "key")))))

-- Replacement preserves position. A tuple loop and a dict loop use the same suite semantics.
example :
    let out := run sortedKeys (denoteSuite enumerateKeys)
    let state := finishState out
    result out = .ok .next ∧ state.iterators = [] ∧
    state.heap[1]? = some ⟨.list ([8, 9, 3, 1, 2].map fun n => .scalar (.int n)), false⟩ :=
  by decide +kernel

example :
    let out := run sortedKeys (denoteSuite (depth := 0)
      (.forIn (localSlot "key") (read "d")
        (.atomic (.setIndex (read "alias") (read "key") (int 9)))))
    let state := finishState out
    result out = .error (.activeIteration 0) ∧ state.iterators = [] ∧
    result (denote (.setIndex (read "alias") (int 3) (int 9)) state) = .ok () :=
  by decide +kernel

end Silmaril.Languages.Starlark.Lists
