module

public import Silmaril.Wasm.Abstract.Function.Defs
public import Silmaril.Wasm.SSA.CoreCert.Defs

/-!
# Equivalence of concrete Wasm callables: the certified λSSA slice

A clean facade for proving equivalence of concrete Core 3.0 functions, and of
anything with a semantics proved equal to a λSSA fragment run relation, such
as a CFG or region interpretation.

* `CallSite H`: a store and a function address, i.e. a concrete callable.
* `callSem P x vs`: its Core 3.0 behaviours on the arguments `vs` (closed host,
  numerics profile `P`), the existing `behaviours`.
* `CallEquiv x y`: on every typed invocation of `x`, under every profile, `x`
  and `y` have the same behaviours, divergence included.

**Scope.** This is an explicit supported subset, not a global claim:

* host: closed (no imports);
* functions: structured native λSSA fragment functions, i.e. the hypotheses of
  `Silmaril.Wasm.SSA.behaviours_eq_run`;
* observation: Core 3.0 behaviours (results, traps, uncaught exceptions,
  divergence) with the final store forgotten.

Within it, `Silmaril.Wasm.Abstract.SSAFragment.Thms` proves the facade
theorems with no further caveat: equivalence from equivalence of fragment run
relations, and equivalence of every certified optimisation.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

/-- A concrete callable: a function address in a store. -/
structure CallSite (H : Type) where
  /-- The store. -/
  store : Store H
  /-- The function address. -/
  addr : Nat

/-- The Core 3.0 behaviours of a call (closed host). -/
def callSem {H : Type} (P : Numerics.Profile) (x : CallSite H) (vs : List Val) :
    Set (Behaviour Val) :=
  behaviours P closedHost x.store x.addr vs

/-- Same behaviours on every typed invocation of `x`, under every profile. -/
def CallEquiv {H H' : Type} (x : CallSite H) (y : CallSite H') : Prop :=
  ∀ (P : Numerics.Profile) (vs : List Val), InvokeOk x.store x.addr vs → callSem P x vs = callSem P y vs

/-- The hypotheses of `Silmaril.Wasm.SSA.behaviours_eq_run` for a call site: a
typed, native, arity-checked store holding the Core code of the structured
native fragment function `f` (from `bf` at type `ft`) at the address. -/
structure IsFragmentSite {H : Type} (x : CallSite H) (ft : FuncType) (bf : Binaryen.BFunc)
    (f : SSA.FragFunc) : Prop where
  storeOk : StoreOk x.store
  nativeOk : NativeFuncsOk x.store.funcs
  storeChk : Silmaril.Wasm.Interp.StoreChk x.store.funcs
  code : ∃ fi : FuncInst H, x.store.funcs[x.addr]? = some fi ∧ fi.code = .wasm (SSA.coreFunc bf) ∧
    Validation.DefType.funcType? fi.type =
      some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal)
  frag : SSA.ofBFunc? ft bf = some f
  native : f.native = true
  structured : Binaryen.BExpr.structuredList bf.body = true

end Silmaril.Wasm.Abstract
