module

public import Silmaril.Wasm.Abstract.Oracle.Thms
public import Silmaril.Wasm.Abstract.RegionCall.Defs

@[expose] public section

/-!
# The native slice of the checked closed oracle

`NativeCallOk s a us`: the guard under which the closed oracle is complete for Core calls
(`MachineClosed/Thms.lean`).
-/

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen

variable {H : Type}

/-- The guard of the native slice: a typed store, native Wasm functions, arity-checked
functions, and a typed invocation. -/
def NativeCallOk (s : Store H) (a : Nat) (us : List Val) : Prop :=
  StoreOk s ∧ NativeFuncsOk s.funcs ∧ Interp.StoreChk s.funcs ∧ InvokeOk s a us

/-- **The checked closed divergence predicate**: a call on the native slice (`NativeCallOk`) that
the closed oracle has no terminating entry for (`closedCall` has no entry whose exit flow, at the
callee's result count, is defined). On the slice this is Core divergence of the call
(`Abstract.closedCall_none_iff_diverges`); outside it (an untyped call, a host function, a store
with invalid functions) it does not hold, so no call is said to diverge falsely. -/
def closedDiv (s : Store H) (a : Nat) (us : List Val) : Prop :=
  NativeCallOk s a us ∧
    ∀ (fi : FuncInst H) (ps rs : List Validation.CValType) (s' : Store H) (bfl : Flow),
      s.funcs[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
      Abstract.closedCall s a us (s', bfl) → Abstract.exitFlow rs.length bfl = none

end Silmaril.Wasm.Cfg.Machine
