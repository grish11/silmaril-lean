module

public import Silmaril.Wasm.Abstract.Closing.Defs
public import Silmaril.Wasm.Abstract.HostEval.Defs
public import Silmaril.Wasm.Abstract.HostCall.Defs

/-!
# Wasm functions with host calls as an open module, closed by `Shape.close` (stage H2)

`Silmaril.Wasm.Abstract.Closing` turns the functions of a store into an open module
`wasmOpen` with no imports: every internal call is a `self` call, recorded with its answer
in the logged run `EvalL`. This module adds the host functions as the **only** import events:

* `wasmHShape H`: imports `wasmHostSig H` (a host function, store and arguments, answered by
  store and result); state the store; a function at every address.
* `wasmHOpen`: a Wasm function's behaviours are those of `wasmOpen` (its `EvalL` log as `self`
  calls, `OCall.lift`); a host function `hh` makes the one import call `(hh, s, vs)`, answered
  arbitrarily by `(s', r)`, and ends as `r` does through its exit flow.
* `wasmEvFun`: the closure `Shape.close wasmHOpen`, as an abstract function of the invocation
  `(a, vs)`. Internal Wasm calls are resolved by the closure and never appear as events; host
  calls appear in execution order with their answers. A host relation then filters the answers
  (`HostRel.Consistent`, `hostObs`).

Theorems in `Silmaril.Wasm.Abstract.HostClosing.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The functions of a store with host calls as imports. -/
abbrev wasmHShape (H : Type) : Silmaril.Games.Abstract.Shape.{0} :=
  ⟨wasmHostSig H, Store H, Nat, fun _ => List Val, fun _ => List Val ⊕ Nat⟩

/-- A recorded call of the open module with host imports. -/
abbrev HCall (H : Type) : Type := Call ((wasmHShape H).E ⊕ₛ (wasmHShape H).self)

/-- An internal call of `wasmOpen`'s log, as a `self` call of `wasmHOpen`. -/
def OCall.lift : OCall H → HCall H
  | ⟨.inr y, ans⟩ => ⟨.inr y, ans⟩

/-- **The functions of a store, host functions as imports.** -/
def wasmHOpen : (wasmHShape H).OpenMod := fun a s vs =>
  {x | (∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (s' : Store H)
      (f₂ : Frame) (bfl fl : Flow) (l : List (OCall H)),
      s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      EvalL s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) l (s', f₂, bfl) ∧
      exitFlow rs.length bfl = some fl ∧ x = (l.map OCall.lift, endOfFlow fl s')) ∨
    (∃ (fi : FuncInst H) (hh : H) (ps rs : List Validation.CValType) (s' : Store H) (r : Result)
      (fl : Flow),
      s.funcs[a]? = some fi ∧ fi.code = .host hh ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      exitFlow rs.length (resFlow r) = some fl ∧
      x = ([⟨.inl (hh, s, vs), (s', r)⟩], endOfFlow fl s'))}

/-- **The logged native semantics of an invocation**: host calls as events, internal calls
closed. -/
def wasmEvFun : AFun (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat) :=
  fun s p => Shape.close wasmHOpen p.1 s p.2

end Silmaril.Wasm.Abstract
