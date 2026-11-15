module

public import Silmaril.Wasm.Interp.XProfile.Defs
public import Silmaril.Proofs.Wasm.Interp.XProfile

/-!
# The instruction profile of the extended arity check: theorems

**Audit of the F4 gates.** The extended adequacy theorems (`OracleX.evalOXT_good`,
`evalOXT_goodT`, `oracleSoundX_closedX`, `oracleSoundT_closedX`, the typed closures and the
examples) assume `StoreChkE ext` and, for closed runs, `GoodStoreX` or `TypedX`/`TypedT`. None
assumes `Binaryen.NativeFuncsOk` or a native-profile check, and every profile `P` is allowed.

* `xInstr_of_flatChkE`: what remains of a profile gate is the extended check's instruction set
  `xInstr`, which is exactly the native one, the annotated `select`, and the five call forms
  (`xInstr_iff`). Floats, vectors, references, tables, memory size/grow/bulk operations,
  exceptions (`throw`, `try_table`) remain outside: F5 and later.
* `t_invoke_outside_native`: the tail example's store is outside the native profile
  (`¬ NativeFuncsOk`), and its tail-calling invocation is still a proved Core 3.0 run.
* Not covered here: hosts (`noHostX` for the typed closures; `closedCallX` answers only
  Wasm callees) and imports, and the converse direction (Core 3.0 runs and divergence of the
  new call forms as `EvalOX` runs), which these soundness theorems do not state.
-/

public section

namespace Silmaril.Wasm.Interp.XProfile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp

/-- **The extended check accepts only `xInstr`.** -/
theorem xInstr_of_flatChkE {H : Type} {ext : ExtArity H} {F : List (FuncInst H)}
    {mi : ModuleInst} {nl ret : Nat} {labels : List Nat} {h : Nat} {i : Instr} {o : Option Nat}
    (hc : flatChkE ext F mi nl ret labels h i = some o) : xInstr i = true :=
  Silmaril.Proofs.Wasm.Interp.XProfile.xInstr_of_flatChkE hc

/-- `xInstr` is the native profile, the annotated `select` and the five call forms. -/
theorem xInstr_iff (i : Instr) :
    xInstr i = true ↔
      Binaryen.nativeInstr i = true ∨ xCallForm i = true ∨ ∃ t, i = .select (some t) :=
  Silmaril.Proofs.Wasm.Interp.XProfile.xInstr_iff i

/-- **A concrete run outside the native profile**: the tail example's store fails
`NativeFuncsOk`, and invoking its function `0` (a `return_call_indirect`) returns `42` in
Core 3.0 at every profile. -/
theorem t_invoke_outside_native :
    ¬ Binaryen.NativeFuncsOk ExampleT.tStore.funcs ∧
      ∀ P : Numerics.Profile,
        Steps P noHostX (invoke ExampleT.tStore 0 []) ⟨ExampleT.tStore, {}, vals [Val.i32 42]⟩ :=
  ⟨Silmaril.Proofs.Wasm.Interp.XProfile.tStore_not_nativeFuncsOk, ExampleT.t_invoke⟩

end Silmaril.Wasm.Interp.XProfile
