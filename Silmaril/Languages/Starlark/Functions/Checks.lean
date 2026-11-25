module

import Silmaril.Languages.Starlark.Functions.Thms
import Silmaril.Languages.Starlark.Lists.Thms
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs
meta import Silmaril.Languages.Starlark.Lists.Denotation.Defs
meta import Silmaril.Languages.Starlark.Lists.Freeze.Defs
meta import Silmaril.Languages.Starlark.Lists.Iteration.Defs

namespace Silmaril.Languages.Starlark.Functions

open Lists (Code State Outcome Error)
open Lists.Iteration (Flow finishState)

deriving instance DecidableEq for Except

private def loc (name : String) : Binding := ⟨.local, name⟩
private def glob (name : String) : Binding := ⟨.global, name⟩
private def read (name : String) : Lists.Expr := .read (.bound (loc name))
private def int (n : Int) : Lists.Expr := .scalar (.int n)
private def values (exprs : List Lists.Expr) : Code (List Lists.Value) :=
  exprs.foldr Code.cons .empty
private def list (exprs : List Lists.Expr) : Lists.Expr := .list (values exprs)
private def tuple (exprs : List Lists.Expr) : Lists.Expr := .tuple (values exprs)
private def call (dst callee : String) (args : List Lists.Expr := []) : Body :=
  .call (some (loc dst)) (read callee) { positional := args }
private def set (name : String) (value : Lists.Expr) : Body :=
  .total (.atomic (.assign (loc name) value))
private def ret (value : Lists.Expr) : Body := .total (.ret value)
private def body (stmts : List Body) : Body := stmts.foldr Body.seq (.total (.atomic .pass))
private def stateWith (bindings : List Binding) : State :=
  bindings.foldl State.allocateSlot {}
private def result {α : Type} : Outcome α → Except Error α
  | .ok a _ => .ok a
  | .error e _ => .error e

private def required (slots : List Binding) : Signature :=
  { positional := slots.map fun slot => ⟨slot, none⟩ }

private def getters : Program := #[
  ⟨required [loc "x"], [loc "get", loc "before"], [], body
    [.define (loc "get") 1, call "before" "get", set "x" (int 2),
     ret (tuple [read "before", read "get"])]⟩,
  ⟨required [], [], [⟨loc "x", loc "x"⟩], ret (read "x")⟩]

-- The first call sees the original value. An escaped closure sees the later write.
#guard
    let code := body [.define (loc "factory") 0, call "pair" "factory" [int 1],
      set "get" (.index (read "pair") (int 1)), call "out" "get"]
    let initial := stateWith ([ "factory", "pair", "get", "out" ].map loc)
    let outcome := run getters code initial
    (result outcome = .ok .next) ∧
    (finishState outcome).bindingValue (loc "out") = .ok (.scalar (.int 2)) ∧
    result (Lists.denote (.index (read "pair") (int 0)) (finishState outcome)) =
      .ok (.scalar (.int 1)) ∧
    (finishState outcome).slots (loc "x") = none

private def moduleReader : Program :=
  #[⟨required [], [], [⟨glob "x", glob "x"⟩], ret (.read (.bound (glob "x")))⟩]

-- The capture acquires the declared slot even before the module initializes it.
#guard
    let initial := stateWith [glob "x", loc "get", loc "out"]
    let define := .define (loc "get") 0
    let fail := run moduleReader (.seq define (call "out" "get")) initial
    let ok := run moduleReader (body [define, .total (.atomic (.assign (glob "x") (int 42))),
      set "x" (int 9), call "out" "get"]) initial
    result fail = .error (.uninitialized (glob "x")) ∧
    (finishState ok).bindingValue (loc "out") = .ok (.scalar (.int 42))

private def reentry : Program := #[
  ⟨required [loc "other"], [loc "f"], [], body [.define (loc "f") 1, ret (read "f")]⟩,
  ⟨required [loc "x"], [loc "out"], [⟨loc "other", loc "other"⟩],
    body [call "out" "other" [read "x"], ret (read "out")]⟩,
  ⟨required [loc "x"], [], [], ret (read "x")⟩]

-- a and b are different closure objects of declaration 1.
#guard
    let initial := stateWith (["maker", "leaf", "a", "b", "out"].map loc)
    let final := run reentry (body [.define (loc "maker") 0, .define (loc "leaf") 2,
      call "b" "maker" [read "leaf"], call "a" "maker" [read "b"], call "out" "a" [int 1]]) initial
    result final = .error (.recursiveCall 1) ∧
    (finishState final).bindingValue (loc "a") ≠ (finishState final).bindingValue (loc "b") ∧
    (finishState final).slots (loc "x") = none

private def sideEffect : Program := #[⟨required [loc "xs"], [], [], .total (.seq
  (.atomic (.eval (.append (read "xs") (int 7))))
  (.ret (.index (read "xs") (int 12))))⟩]

#guard
    let initial := stateWith (["f", "container", "out"].map loc)
    let final := run sideEffect (body [.define (loc "f") 0, set "container" (list []),
      call "out" "f" [read "container"]]) initial
    let state := finishState final
    result final = .error (.indexRange 12 1) ∧ state.slots (loc "xs") = none ∧
    result (Lists.denote (.index (read "container") (int 0)) state) = .ok (.scalar (.int 7))

private def makers : Program := #[
  ⟨required [], [loc "xs", loc "appender"], [], body [set "xs" (list []),
    .define (loc "appender") 1, ret (read "appender")]⟩,
  ⟨required [], [], [⟨loc "xs", loc "xs"⟩],
    .total (.atomic (.eval (.append (read "xs") (int 1))))⟩]

#guard
    let initial := stateWith (["factory", "f", "out"].map loc)
    let ready := finishState (run makers (body [.define (loc "factory") 0, call "f" "factory"]) initial)
    let roots := (ready.bindingValue (loc "f")).toOption.toList
    let out := run makers (call "out" "f") (ready.freeze roots)
    result out = .error (.frozen 6)

end Silmaril.Languages.Starlark.Functions
