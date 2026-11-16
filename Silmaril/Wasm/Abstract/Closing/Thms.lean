module

public import Silmaril.Wasm.Abstract.Closing.Defs
public import Silmaril.Wasm.Abstract.Function.Defs
public import Silmaril.Wasm.Abstract.Recursion.Thms
import Silmaril.Proofs.Wasm.Abstract.Closing.Basic
import Silmaril.Proofs.Wasm.Abstract.Closing.Core
import Silmaril.Proofs.Wasm.Abstract.Closing.Descent

/-!
# Wasm functions as an open abstract module: theorems

**Closure agreement.** The generic closing of abstract modules
(`Silmaril.Games.Abstract.Shape.close`, the least fixpoint of resolving
internal calls), applied to the open module of a store's functions, gives
exactly the closed outcomes of `Silmaril.Wasm.Abstract.Recursion`
(`close_wasmOpen`). Those are the terminating runs of the native recursive
semantics: no import calls; returns and exceptions with the final store;
traps; never `div`. This holds for every store, typed or not.

**Against Core 3.0.** With the closed host, on typed, native, arity-checked
stores, at every profile, the Core 3.0 abstract function of an address
(`wasmFun`) is the closure, plus `div` exactly when the closure is empty
(`wasmFun_eq_close`). Its other ingredient is `diverges_iff`: Core divergence
of an invocation is the absence of closed outcomes.

**Scope.**

* **`closeD` is sound, not complete.** An infinite internal-call chain
  rules out every closed outcome of its first call
  (`no_closedOutcome_of_divChain`, any store). So the `div` that `closeD` adds
  is Core divergence, and under the Core hypotheses
  `closeD wasmOpen ⊆ wasmFun` (`closeD_subset_wasmFun`). The converse fails
  for loops without calls, which have no chain (see
  `Silmaril.Wasm.Abstract.SelfLoop` for a recursion where the two agree).
* Imports are absent (`Sig.empty`); the host is `closedHost`.
* Only direct `call`s are exposed as internal calls. The Core results hold
  on the native profile (`NativeFuncsOk`: every function in the store is Wasm
  code whose instructions are in `instrInNativeProfile`). That excludes host
  functions and every instruction outside the profile.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **Closing the open module gives the closed outcomes.** -/
theorem close_wasmOpen (a : Nat) (s : Store H) (vs : List Val) :
    Shape.close wasmOpen a s vs =
      {y | ∃ s' fl, ClosedOutcome s a vs s' fl ∧ y = ([], endOfFlow fl s')} :=
  Silmaril.Proofs.Wasm.Abstract.Closing.close_wasmOpen a s vs

/-- Core 3.0 divergence of a native invocation is the absence of closed
outcomes. -/
theorem diverges_iff_no_closedOutcome {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    Diverges P closedHost (invoke s a vs) ↔ ∀ s' fl, ¬ ClosedOutcome s a vs s' fl :=
  Silmaril.Proofs.Wasm.Abstract.Closing.diverges_iff hs hF hS hok P

/-- **Core 3.0 functions are the closure of the open module**, plus divergence
exactly when the closure is empty. -/
theorem wasmFun_eq_close {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    wasmFun P closedHost a s vs =
      Shape.close wasmOpen a s vs ∪ {x | x = ([], .div) ∧ Shape.close wasmOpen a s vs = ∅} :=
  Silmaril.Proofs.Wasm.Abstract.Closing.wasmFun_eq_close hs hF hS hok P

/-- **An infinite internal-call chain has no closed outcome.** The proof is
by induction on the recursive derivation; the semantics is deterministic. -/
theorem no_closedOutcome_of_divChain {s : Store H} {a : Nat} {vs : List Val}
    {qs : List (Call Sig.empty)}
    (h : Shape.DivChain wasmOpen (Shape.close wasmOpen) ⟨a, (vs, s)⟩ qs) (s' : Store H) (fl : Flow) :
    ¬ ClosedOutcome s a vs s' fl :=
  Silmaril.Proofs.Wasm.Abstract.Closing.no_closedOutcome_of_divChain h s' fl

/-- So a call starting an infinite internal-call chain has nothing in `close`. -/
theorem close_eq_empty_of_divChain {s : Store H} {a : Nat} {vs : List Val}
    {qs : List (Call Sig.empty)}
    (h : Shape.DivChain wasmOpen (Shape.close wasmOpen) ⟨a, (vs, s)⟩ qs) :
    Shape.close wasmOpen a s vs = ∅ := by
  rw [close_wasmOpen, Set.eq_empty_iff_forall_notMem]
  rintro _ ⟨s', fl, hc, -⟩
  exact no_closedOutcome_of_divChain h s' fl hc

/-- **`closeD` is sound for Core 3.0**: under the Core hypotheses, every
behaviour it gives is a behaviour of `wasmFun`. -/
theorem closeD_subset_wasmFun {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    Shape.closeD wasmOpen a s vs ⊆ wasmFun P closedHost a s vs :=
  Silmaril.Proofs.Wasm.Abstract.Closing.closeD_subset_wasmFun hs hF hS hok P

end Silmaril.Wasm.Abstract
