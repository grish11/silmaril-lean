module

public import Silmaril.Wasm.Interp.Example.Defs
public import Silmaril.Proofs.Wasm.Interp.Check
public import Silmaril.Wasm.Binaryen.AdequacyModule
public import Silmaril.Wasm.SingleThreaded.Soundness
public import Silmaril.Proofs.Wasm.Interp.Closed

@[expose] public section

/-!
# A closed module for native adequacy (proofs)

The validation, the allocation and the store of `exMod` are computed by kernel evaluation of
silmaril-lean's `validate?` and `prepare?` (`decide +kernel` on Boolean summaries; no
compiled evaluation), and so are the executable checks `nativeFuncsB` and `storeChkB` and two runs
of the native interpreter. The typing of the store comes from silmaril-lean's
`prepare?_sound` and `Instantiate.ok`. New proofs.
-/

namespace Silmaril.Proofs.Wasm.Interp.Example

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp Silmaril.Wasm.Interp.Example

/-- `exMod` validates, without imports. -/
theorem exMod_valid : ((Validation.validate? exMod).map fun mt => mt.imports.isEmpty) = some true :=
  by decide +kernel
/-- The allocation succeeds. -/
theorem exPrep_some : (prepare? evalConst? ({} : Store Empty) exMod []).isSome = true :=
  by decide +kernel
/-- No segment code and no start function. -/
theorem exPrep_shape : exPrep.1.code.isEmpty = true ∧ exPrep.2.isNone = true := by decide +kernel
/-- The executable native-profile check. -/
theorem exStore_native : nativeFuncsB exStore.funcs = true := by decide +kernel
/-- The executable arity check. -/
theorem exStore_chk : storeChkB exStore.funcs = true := by decide +kernel
/-- The type of function `0`. -/
theorem exStore_type : (exStore.funcs[0]?.bind fun fi => Validation.DefType.funcType? fi.type) =
    some ([.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]) := by decide +kernel
/-- Two native runs. -/
theorem exRun_07 : ((Binaryen.invokeRun 20 exStore 0 [Val.i32 0, Val.i32 7]).bind
    fun r => Binaryen.flowBeh r.2) = some (.returns [Val.i32 7]) := by decide +kernel
theorem exRun_37 : ((Binaryen.invokeRun 20 exStore 0 [Val.i32 3, Val.i32 7]).bind
    fun r => Binaryen.flowBeh r.2) = some (.returns [Val.i32 3]) := by decide +kernel

/-- The allocation, as an equation. -/
theorem exPrep_eq : prepare? evalConst? ({} : Store Empty) exMod [] = some exPrep := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp exPrep_some
  simp [exPrep, hp]

/-- **`exMod` instantiates to `exPrep.1`**, at every profile and host. -/
theorem ex_instantiate (P : Numerics.Profile) (host : HostSemantics Empty) :
    Instantiate P host ({} : Store Empty) exMod [] exPrep.1 :=
  Closed.instantiate_of_prepare exMod_valid exPrep_eq
    (Option.isNone_iff_eq_none.mp exPrep_shape.2) P host

/-- **The store of the instance is typed.** -/
theorem exStore_ok : StoreOk exStore :=
  Closed.storeOk_of_prepare exMod_valid exPrep_eq (Option.isNone_iff_eq_none.mp exPrep_shape.2)

/-- **Two `i32` arguments are a typed invocation of function `0`.** -/
theorem ex_invokeOk (x y : BitVec 32) : InvokeOk exStore 0 [Val.i32 x, Val.i32 y] := by
  obtain ⟨fi, hfi, hty⟩ : ∃ fi, exStore.funcs[0]? = some fi ∧
      Validation.DefType.funcType? fi.type =
        some ([.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]) := by
    rcases h : exStore.funcs[0]? with _ | fi
    · have ht := exStore_type
      simp [h] at ht
    · exact ⟨fi, rfl, by simpa [h] using exStore_type⟩
  unfold Validation.DefType.funcType? at hty
  split at hty
  · rename_i ps rs he
    simp only [Option.some.injEq, Prod.mk.injEq] at hty
    refine ⟨fi, ps, rs, hfi, Validation.Expand.iff.mpr he, ?_⟩
    rw [hty.1]
    exact .cons (ValOk.num _) (.cons (ValOk.num _) .nil)
  · cases hty

/-! ## Native behaviours of a terminating invocation -/

/-- More fuel never changes a result of `invokeRun` (`Closed.invokeRun_mono`). -/
theorem invokeRun_mono {H : Type} {n n' : Nat} (hle : n ≤ n') {s : Store H} {a : Nat}
    {vs : List Val} {r : Store H × Binaryen.Flow} (h : Binaryen.invokeRun n s a vs = some r) :
    Binaryen.invokeRun n' s a vs = some r :=
  Closed.invokeRun_mono hle h

/-- **The native behaviours of a terminating invocation** are its single result
(`Closed.nbeh_eq_singleton`). -/
theorem nbeh_eq_singleton {H : Type} {s : Store H} {a : Nat} {vs : List Val} {n : Nat}
    {b : Behaviour Val} (h : ((Binaryen.invokeRun n s a vs).bind fun r => Binaryen.flowBeh r.2) =
      some b) : Binaryen.nbeh s a vs = {b} :=
  Closed.nbeh_eq_singleton h

end Silmaril.Proofs.Wasm.Interp.Example
