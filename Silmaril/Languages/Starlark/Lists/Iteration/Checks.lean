module

import Silmaril.Languages.Starlark.Lists.Iteration.Thms

namespace Silmaril.Languages.Starlark.Lists.Iteration

deriving instance DecidableEq for Except

private def localSlot (name : String) : Binding := ⟨.local, name⟩
private def read (name : String) : Expr := .read (.bound (localSlot name))
private def int (n : Int) : Expr := .scalar (.int n)
private def list (items : List Expr) : Expr := .list (items.foldr Code.cons .empty)
private def assign (name : String) (v : Expr) : Stmt := .assign (localSlot name) v
private def append (name : String) (v : Expr) : Stmt := .eval (.append (read name) v)
private def items (state : State) (address : Address) : Option (List Value) :=
  state.heap[address]?.bind fun cell =>
    match cell.contents with
    | .list elements => some elements
    | _ => none

private def result {α : Type} : Outcome α → Except Error α
  | .ok a _ => .ok a
  | .error e _ => .error e

private def setup : Stmt :=
  .seq (assign "a" (list [int 1, int 0, int 2]))
    (.seq (assign "alias" (read "a")) (assign "out" (list [])))

private def run (code : Suite 0) (stack : List Address := []) : Outcome Flow :=
  Outcome.resume (denote setup { iterators := stack }) fun () => denoteSuite code

-- Continue and break consume only the current iteration's control.
example :
    let out := run (.seq
      (.forList (localSlot "x") (read "a")
        (.branch (read "x") (.seq (.atomic (append "out" (read "x"))) .continueLoop) .breakLoop))
      (.seq (.atomic (append "alias" (int 7))) (.ret (read "x"))))
    result out = .ok (.returned (.scalar (.int 0))) ∧
    (finishState out).iterators = [] ∧
    items (finishState out) 0 = some ([1, 0, 2, 7].map fun n => .scalar (.int n)) ∧
    items (finishState out) 1 = some [.scalar (.int 1)] :=
  by decide +kernel

-- Skipping every body remainder exhausts the list and releases the iterator.
example :
    let out := run (.seq
      (.forList (localSlot "x") (read "a")
        (.seq .continueLoop (.atomic (append "alias" (int 9)))))
      (.atomic (append "a" (int 7))))
    result out = .ok .next ∧ (finishState out).iterators = [] ∧
    (finishState out).bindings (localSlot "x") = some (.scalar (.int 2)) ∧
    items (finishState out) 0 = some ([1, 0, 2, 7].map fun n => .scalar (.int n)) :=
  by decide +kernel

-- Breaking the inner loop on the same address leaves the outer guard active.
-- Failure releases it and preserves the earlier mutation to the other list.
example :
    let out := run (.forList (localSlot "x") (read "a")
      (.seq (.forList (localSlot "y") (read "alias") .breakLoop)
        (.seq (.atomic (append "out" (read "x")))
          (.atomic (.setIndex (read "alias") (int 0) (int 9)))))) [99]
    result out = .error (.activeIteration 0) ∧ (finishState out).iterators = [99] ∧
    items (finishState out) 1 = some [.scalar (.int 1)] ∧
    result (denote (append "alias" (int 9)) (finishState out)) = .ok () :=
  by decide +kernel

-- Two simultaneously active iterators on the same address unwind on an error.
example :
    let out := run (.forList (localSlot "x") (read "a")
      (.forList (localSlot "y") (read "alias") (.atomic (append "alias" (int 9)))))
    result out = .error (.activeIteration 0) ∧ (finishState out).iterators = [] :=
  by decide +kernel

example :
    let out := run (.seq
      (.forList (localSlot "x") (read "a")
        (.forList (localSlot "y") (list [int 12]) (.ret (read "y"))))
      (.atomic (.eval (.index (read "out") (int 0))))) [99]
    result out = .ok (.returned (.scalar (.int 12))) ∧ (finishState out).iterators = [99] ∧
    (finishState out).heap.size = 3 :=
  by decide +kernel

example :
    let out := run (.forList (localSlot "x") (read "a")
      (.forList (localSlot "y") (read "alias") (.atomic (.eval (.index (read "out") (int 0)))))) [99]
    result out = .error (.indexRange 0 0) ∧ (finishState out).iterators = [99] :=
  by decide +kernel

example :
    result (run (.forList (localSlot "x") (int 1) .breakLoop)) = .error .notIterable ∧
    result (run (.forList (localSlot "x") (read "out") (.ret (int 1)))) = .ok .next :=
  by decide +kernel

end Silmaril.Languages.Starlark.Lists.Iteration
