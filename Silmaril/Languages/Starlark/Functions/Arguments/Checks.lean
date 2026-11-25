module

import Silmaril.Languages.Starlark.Functions.Thms
import Silmaril.Languages.Starlark.Lists.Thms
meta import Silmaril.Languages.Starlark.Functions.Arguments.Defs
meta import Silmaril.Languages.Starlark.Functions.Defs
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs
meta import Silmaril.Languages.Starlark.Lists.Denotation.Defs
meta import Silmaril.Languages.Starlark.Lists.Freeze.Defs
meta import Silmaril.Languages.Starlark.Lists.Iteration.Defs

namespace Silmaril.Languages.Starlark.Functions

open Lists (Code State Outcome Error)
open Lists.Iteration (Flow finishState)

deriving instance DecidableEq for Except

private def slot (name : String) : Binding := ⟨.local, name⟩
private def name (n : String) : Lists.Expr := .read (.bound (slot n))
private def int (n : Int) : Lists.Expr := .scalar (.int n)
private def list (xs : List Lists.Expr) : Lists.Expr := .list (operandList xs)
private def tup (xs : List Lists.Expr) : Lists.Expr := .tuple (operandList xs)
private def dict (xs : List (Lists.Expr × Lists.Expr)) : Lists.Expr :=
  .dict (xs.foldl (fun entries (k, v) => .entry entries k v) .noEntries)
private def param (n : String) (defaultExpr : Option Lists.Expr := none) : Parameter :=
  ⟨slot n, defaultExpr⟩
private def append (n : String) (v : Lists.Expr) : Lists.Expr := .append (name n) v
private def set (n : String) (v : Lists.Expr) : Body := .total (.atomic (.assign (slot n) v))
private def ret (v : Lists.Expr) : Body := .total (.ret v)
private def seq (body : List Body) : Body := body.foldr Body.seq (.total (.atomic .pass))
private def frame (slots : List String) : State := (slots.map slot).foldl State.allocateSlot {}
private def result {α : Type} : Outcome α → Except Error α
  | .ok a _ => .ok a
  | .error e _ => .error e

private def signature : Signature :=
  { positional := [param "a", param "b" (int 2)]
    keywordOnly := [param "c", param "d" (int 4)]
    varargs := some (slot "rest"), kwargs := some (slot "kw") }

private def invoke (args : Arguments) : Body := .call (some (slot "out")) (name "f") args

private def packed : Program :=
  #[⟨signature, [], [], ret (tup (["a", "b", "rest", "c", "d", "kw"].map name))⟩]

private def invokePacked (args : Arguments) : Outcome Flow :=
  run packed (.seq (.define (slot "f") 0) (invoke args)) (frame ["f", "out"])

-- A named argument can occur before *args. The remaining names keep call order.
#guard
  let out := invokePacked
    { positional := [int 1], keywords := [("c", int 5), ("y", int 9)]
      star := list [int 3, int 7], starStar := dict [(.string "z", int 8)] }
  let state := finishState out
  let read := fun i => Lists.denote (.index (name "out") (int i)) state
  result out = .ok .next ∧
  result (read 0) = .ok (.scalar (.int 1)) ∧ result (read 1) = .ok (.scalar (.int 3)) ∧
  result (read 3) = .ok (.scalar (.int 5)) ∧ result (read 4) = .ok (.scalar (.int 4)) ∧
  result (Lists.denote (.index (.index (name "out") (int 2)) (int 0)) state) =
    .ok (.scalar (.int 7)) ∧
  result (Lists.denote (.index (.index (name "out") (int 5)) (.string "z")) state) =
    .ok (.scalar (.int 8))

#guard
  result (invokePacked { positional := [int 1] }) = .error (.missingArguments ["c"]) ∧
  result (invokePacked { positional := [int 1], keywords := [("a", int 2)] }) =
    .error (.multipleArgumentValues "a") ∧
  result (invokePacked { positional := [int 1], keywords := [("c", int 2)], starStar := dict [(.string "c", int 3)] }) = .error (.multipleArgumentValues "c") ∧
  result (invokePacked { keywords := [("x", int 2)], starStar := dict [(.string "x", int 3)] }) = .error (.multipleArgumentValues "x") ∧
  result (invokePacked { star := some (int 1) }) = .error .invalidStar ∧
  result (invokePacked { starStar := some (list []) }) = .error .invalidStarStar ∧
  result (invokePacked { star := some (int 1), starStar := dict [(int 3, int 7)] }) =
    .error (.keywordMustBeString (.scalar (.int 3)))

-- Expansion validation follows evaluation of every operand in source order.
#guard
  let code : Body := seq
    [set "events" (list []), .define (slot "f") 0,
     invoke { positional := [append "events" (int 1)]
              keywords := [("c", append "events" (int 2))]
              star := list [append "events" (int 3)]
              starStar := dict [(int 3, append "events" (int 4))] }]
  let out := run packed code (frame ["events", "f", "out"])
  let state := finishState out
  result out = .error (.keywordMustBeString (.scalar (.int 3))) ∧
  (match state.bindingValue (slot "events") with
   | .ok (.list address) => decide (result (Lists.listElements address state) =
       .ok ([1, 2, 3, 4].map fun n => .scalar (.int n)))
   | _ => false) = true

private def bare : Signature :=
  { positional := [param "a"], keywordOnly := [param "b" (int 2), param "c"] }

#guard
  (bindArguments bare [] ⟨[.scalar (.int 1), .scalar (.int 2)], []⟩ |>.isOk) = false ∧
  (match bindArguments bare [] ⟨[.scalar (.int 1)], [("other", .scalar .none)]⟩ with
   | .error (.unexpectedKeyword "other") => true
   | _ => false) = true

#guard
  (match runChecked packed
    (.branch (int 0) (invoke { keywords := [("c", int 1), ("c", int 2)] }) (ret (int 0))) with
   | .error (.duplicateExplicitKeyword "c") => true
   | _ => false) = true ∧
  Signature.validate { positional := [param "x", param "x"] } =
    .error (.duplicateParameter "x") ∧
  Signature.validate { positional := [param "x" (int 1), param "y"] } =
    .error (.requiredAfterDefault "y") ∧
  Signature.validate { keywordOnly := [param "x"] } = .error .bareStarWithoutOptional

private def defaulted : Program := #[⟨
  { positional := [param "xs" (list []), param "stamp" (append "counter" (int 4))] },
  [], [], .total (.seq (.atomic (.eval (append "xs" (int 1)))) (.ret (name "xs")))⟩]

-- The counter default runs at definition. Both calls share the same list default.
#guard
  let code : Body := seq
    [set "counter" (list []), .define (slot "f") 0,
     .call (some (slot "a")) (name "f") {}, invoke {}]
  let out := run defaulted code (frame ["counter", "f", "a", "out"])
  let state := finishState out
  let roots := (state.bindingValue (slot "f")).toOption.toList
  result out = .ok .next ∧ state.bindingValue (slot "a") = state.bindingValue (slot "out") ∧
  result (Lists.denote (.index (name "counter") (int 0)) state) = .ok (.scalar (.int 4)) ∧
  result (Lists.denote (.index (name "counter") (int 1)) state) = .error (.indexRange 1 1) ∧
  result (Lists.denote (.index (name "out") (int 1)) state) = .ok (.scalar (.int 1)) ∧
  (match result (run defaulted (invoke {}) (state.freeze roots)) with
   | .error (.frozen _) => true
   | _ => false) = true

end Silmaril.Languages.Starlark.Functions
