module

public import Silmaril.Wasm.Abstract.SelfLoop.Defs
public import Silmaril.Wasm.Abstract.Closing.Thms
public import Silmaril.Wasm.Abstract.Function.Defs
import Silmaril.Proofs.Wasm.Abstract.SelfLoop.Basic
import Silmaril.Proofs.Wasm.Abstract.SelfLoop.Example

/-!
# Unbounded recursion: theorems

For a function whose body is `call` to itself (`SelfLoop`), on any store:

* `selfLoop_close`: the least-fixpoint closing `Shape.close wasmOpen` gives it
  **no behaviour**. It has no closed outcome (`selfLoop_no_closedOutcome`),
  since every recursive derivation of the call contains another one.
* `selfLoop_closeD`: `Shape.closeD wasmOpen` gives it **exactly `div`**,
  through the constant infinite internal-call chain.
* `selfLoop_wasmFun`: with the Core hypotheses of `wasmFun_eq_close`, the
  Core 3.0 abstract function is exactly `div` as well.

So on self-loops `closeD` agrees with Core 3.0 and `close` does not: the
Wasm form of `Silmaril.Games.Abstract.Shape.exists_close_omits_div`. That
agreement is **not** a general theorem. `closeD` adds `div` only along
internal-call chains, so it has nothing to add for a body that loops without
any call (`loop (br 0)`), although Core diverges there. That example is not
formalised here.

**Non-vacuity.** `recMod`, `(module (type (func)) (func (type 0) (call 0)))`,
validates and instantiates (`rec_instantiate`, every profile and host). Every
hypothesis holds on its store (`recStore_ok`, `rec_invokeOk`; the native and
arity checks `recStore_nativeFuncsOk`, `recStore_storeChk` and `selfLoopB` by kernel
evaluation). Its function is exactly
`div` in Core 3.0 at every profile (`rec_wasmFun`), and in `closeD`
(`rec_closeD`), and has nothing in `close` (`rec_close`).
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The executable check is sound. -/
theorem selfLoop_of_check {s : Store H} {a : Nat} (h : selfLoopB s a = true) : SelfLoop s a :=
  Silmaril.Proofs.Wasm.Abstract.SelfLoop.selfLoop_of_selfLoopB h

/-- A self-looping function has no closed outcome. -/
theorem selfLoop_no_closedOutcome {s : Store H} {a : Nat} (h : SelfLoop s a) (vs : List Val)
    (s' : Store H) (fl : Flow) : ¬ ClosedOutcome s a vs s' fl :=
  Silmaril.Proofs.Wasm.Abstract.SelfLoop.no_closedOutcome h vs s' fl

/-- **`close` gives a self-looping function no behaviour.** -/
theorem selfLoop_close {s : Store H} {a : Nat} (h : SelfLoop s a) (vs : List Val) :
    Shape.close wasmOpen a s vs = ∅ :=
  Silmaril.Proofs.Wasm.Abstract.SelfLoop.close_eq_empty h vs

/-- **`closeD` gives a self-looping function exactly divergence.** -/
theorem selfLoop_closeD {s : Store H} {a : Nat} (h : SelfLoop s a) (vs : List Val) :
    Shape.closeD wasmOpen a s vs = {([], .div)} :=
  Silmaril.Proofs.Wasm.Abstract.SelfLoop.closeD_eq h vs

/-- **Core 3.0 gives a self-looping function exactly divergence.** -/
theorem selfLoop_wasmFun {s : Store H} {a : Nat} (h : SelfLoop s a) {vs : List Val}
    (hs : StoreOk s) (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    wasmFun P closedHost a s vs = {([], .div)} :=
  Silmaril.Proofs.Wasm.Abstract.SelfLoop.wasmFun_eq h hs hF hS hok P

/-- `recMod` instantiates to `recPrep.1`, at every profile and host. -/
theorem rec_instantiate (P : Numerics.Profile) (host : HostSemantics Empty) :
    Instantiate P host ({} : Store Empty) recMod [] recPrep.1 :=
  Silmaril.Proofs.Wasm.Abstract.SelfLoop.Example.rec_instantiate P host

theorem recStore_ok : StoreOk recStore := Silmaril.Proofs.Wasm.Abstract.SelfLoop.Example.recStore_ok

theorem recStore_nativeFuncsOk : NativeFuncsOk recStore.funcs :=
  Silmaril.Wasm.Interp.nativeFuncsOk_of_check Silmaril.Proofs.Wasm.Abstract.SelfLoop.Example.recStore_native

theorem recStore_storeChk : Silmaril.Wasm.Interp.StoreChk recStore.funcs :=
  Silmaril.Wasm.Interp.storeChk_of_check Silmaril.Proofs.Wasm.Abstract.SelfLoop.Example.recStore_chk

theorem recStore_funcType : (recStore.funcs[0]?.bind fun fi => Validation.DefType.funcType? fi.type) =
    some ([], []) :=
  Silmaril.Proofs.Wasm.Abstract.SelfLoop.Example.recStore_type

theorem rec_invokeOk : InvokeOk recStore 0 [] :=
  Silmaril.Proofs.Wasm.Abstract.SelfLoop.Example.rec_invokeOk

theorem rec_selfLoop : SelfLoop recStore 0 :=
  Silmaril.Proofs.Wasm.Abstract.SelfLoop.Example.rec_selfLoop

/-- **`(func (call 0))` diverges in Core 3.0**, at every profile, and does nothing else. -/
theorem rec_wasmFun (P : Numerics.Profile) : wasmFun P closedHost 0 recStore [] = {([], .div)} :=
  Silmaril.Proofs.Wasm.Abstract.SelfLoop.Example.rec_wasmFun P

/-- `close` misses its divergence. -/
theorem rec_close : Shape.close wasmOpen 0 recStore [] = ∅ := selfLoop_close rec_selfLoop []

/-- `closeD` sees it. -/
theorem rec_closeD : Shape.closeD wasmOpen 0 recStore [] = {([], .div)} :=
  selfLoop_closeD rec_selfLoop []

end Silmaril.Wasm.Abstract
