module

public import Silmaril.Wasm.Interp.ExampleX.Defs
public import Silmaril.Wasm.Interp.OracleX.Thms
public import Silmaril.Wasm.Binaryen.AdequacyModule
public import Silmaril.Wasm.SingleThreaded.Soundness
public import Silmaril.Wasm.Binaryen.Pass.DirectizeCast
public import Silmaril.Wasm.Execution.Core.Soundness.PresCall

@[expose] public section

/-!
# A store whose function makes an indirect call (proofs)

The validation and the allocation of `xMod` are computed by kernel evaluation
(`decide +kernel`; no compiled evaluation), and so are the executable extended store
check and the indirect-call check. The typing of the store comes from `prepare?_sound` and
`Instantiate.ok`. The closed extended run of function `0` (an indirect call into function
`1`) is built by hand; its Core 3.0 behaviour, an invocation returning `42`, follows from the
soundness of the closure (`oracleSoundX_closedX`).
-/

namespace Silmaril.Proofs.Wasm.Interp.ExampleX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp Silmaril.Wasm.Interp.ExampleX
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.XRecursion

theorem storeChkE_of_storeChkEB {H : Type} {ext : ExtArity H} {F : List (FuncInst H)}
    (h : storeChkEB ext F = true) : StoreChkE ext F := by
  intro a fi fn ps rs hfi hcode hty
  have hb : funcChkEB ext F fi = true := List.all_eq_true.mp h fi (List.mem_of_getElem? hfi)
  simpa only [funcChkEB, hcode, hty] using hb

/-- `xMod` validates, without imports. -/
theorem xMod_valid : ((Validation.validate? xMod).map fun mt => mt.imports.isEmpty) = some true :=
  by decide +kernel
/-- The allocation succeeds. -/
theorem xPrep_some : (prepare? evalConst? ({} : Store Empty) xMod []).isSome = true :=
  by decide +kernel
/-- No segment code and no start function. -/
theorem xPrep_shape : xPrep.1.code.isEmpty = true ∧ xPrep.2.isNone = true := by decide +kernel
/-- **The extended store check passes**: the store's function with `call_indirect` is checked by
`irExt` (the native check rejects it). -/
theorem xStore_chkEB : storeChkEB irExt xStore.funcs = true := by decide +kernel
/-- The native store check fails: the example is outside the native profile. -/
theorem xStore_not_chkB : storeChkB xStore.funcs = false := by decide +kernel
/-- Every body has no `call_ref`, and its indirect calls name instance types. -/
theorem xStore_indB : (xStore.funcs.all fun fi => match fi.code with
    | .wasm fn => indOkL fi.module (Binaryen.liftInstrs fn.body)
    | .host _ => true) = true := by decide +kernel

theorem xPrep_eq : prepare? evalConst? ({} : Store Empty) xMod [] = some xPrep := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp xPrep_some
  simp [xPrep, hp]

/-- **`xMod` instantiates to `xPrep.1`**, at every profile and host. -/
theorem x_instantiate (P : Numerics.Profile) (host : HostSemantics Empty) :
    Instantiate P host ({} : Store Empty) xMod [] xPrep.1 := by
  obtain ⟨mt, hmt, hnil⟩ : ∃ mt, Validation.validate? xMod = some mt ∧ mt.imports.isEmpty := by
    rcases h : Validation.validate? xMod with _ | mt
    · have hm := xMod_valid
      simp [h] at hm
    · have hm := xMod_valid
      simp only [h, Option.map_some, Option.some.injEq] at hm
      exact ⟨mt, rfl, hm⟩
  have himp : mt.imports = [] := List.isEmpty_iff.mp hnil
  have hvalid : ∃ xtE xtI, Validation.ModuleOk xMod ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk ({} : Store Empty)) [] xtI :=
    ⟨mt.exports, mt.imports, by simpa using Validation.validate?_sound hmt, by rw [himp]; exact .nil⟩
  have hst : xPrep.2 = none := Option.isNone_iff_eq_none.mp xPrep_shape.2
  have h : Instantiate P host ({} : Store Empty) xMod [] (xPrep.1.withStart xPrep.2) :=
    (prepare?_sound (P := P) (host := host) (c := xPrep.1) (st := xPrep.2) evalConst?_evalSound
      xPrep_eq hvalid).2
  have hw : xPrep.1.withStart xPrep.2 = xPrep.1 := by rw [hst]; rfl
  rwa [hw] at h

/-- **The store of the instance is typed.** -/
theorem xStore_ok : StoreOk xStore := by
  have hc : ConfigOk xPrep.1 [] :=
    Instantiate.ok SingleThreaded.divHost_ok Binaryen.storeOk_empty
      (x_instantiate (SingleThreaded.profile fun _ _ _ _ => false) SingleThreaded.divHost)
  exact SingleThreaded.ConfigOk.storeOk hc

/-- Valid instance types of a typed store's Wasm functions. -/
theorem tyTypes_of_storeOk {H : Type} {s : Store H} (hs : StoreOk s) {a : Nat} {fi : FuncInst H}
    {fn : Func} (hfi : s.funcs[a]? = some fi) (hc : fi.code = .wasm fn) : TyTypes fi.module := by
  cases hs.funcs fi (List.mem_of_getElem? hfi) with
  | wasm _ hm _ _ _ =>
    obtain ⟨-, -, -, ht⟩ := ModuleInstOk.ctx_fields hm
    intro y d hd
    exact PC.TypesOk.get (PC.ModuleInstOk.typesOk' hm) (x := y)
      (by simpa [Validation.Context.toTypeCtx, ht] using hd)
  | host _ _ hc' => rw [hc] at hc'; cases hc'

/-- **The store is good** for the closure's soundness. -/
theorem xStore_good : GoodStoreX xStore := by
  refine ⟨fun a fi hfi => PC.StoreOk.func_tyOk xStore_ok hfi, fun a fi fn hfi hc => ?_⟩
  refine ⟨tyTypes_of_storeOk xStore_ok hfi hc, ?_⟩
  have hb := List.all_eq_true.mp xStore_indB fi (List.mem_of_getElem? hfi)
  simpa only [hc] using hb

/-- The instance of the two functions. -/
abbrev xMI : ModuleInst := (xStore.funcs[0]?.map (·.module)).getD {}

/-- The callee's code. -/
abbrev f1 : Func := ⟨⟨0⟩, [], [.intConst .i32 42]⟩

/-- The caller's code. -/
abbrev f0 : Func := ⟨⟨0⟩, [], [.intConst .i32 0, .callIndirect ⟨0⟩ ⟨0⟩]⟩

theorem fi1_spec : ∃ fi : FuncInst Empty, xStore.funcs[1]? = some fi ∧ fi.code = .wasm f1 ∧
    Validation.DefType.funcType? fi.type = some ([], [.num (.int .i32)]) ∧
    xMI.types[0]? = some fi.type :=
  ⟨_, rfl, rfl, rfl, rfl⟩

theorem fi0_spec : ∃ fi : FuncInst Empty, xStore.funcs[0]? = some fi ∧ fi.code = .wasm f0 ∧
    Validation.DefType.funcType? fi.type = some ([], [.num (.int .i32)]) ∧ fi.module = xMI :=
  ⟨_, rfl, rfl, rfl, rfl⟩

/-- **The closed extended run of the callee**: `42`. -/
theorem x_callee : closedCallX xStore 1 [] (xStore, .normal [Val.i32 42]) := by
  obtain ⟨fi, hfi, hc, hty, -⟩ := fi1_spec
  rw [closedCallX_fixpoint]
  refine ⟨fi, f1, [], [.num (.int .i32)], Frame.forCall fi.module [] f1.locals, hfi, hc, hty, ?_⟩
  exact .opOk (fun x h => by cases h) .nil rfl .nil

/-- **The closed extended run of the caller**: an indirect call into the table's slot `0`,
which holds function `1`. -/
theorem x_caller : closedCallX xStore 0 [] (xStore, .normal [Val.i32 42]) := by
  obtain ⟨fi1, hfi1, hc1, hty1, hy1⟩ := fi1_spec
  obtain ⟨fi, hfi, hc, hty, hm⟩ := fi0_spec
  rw [closedCallX_fixpoint]
  refine ⟨fi, f0, [], [.num (.int .i32)], Frame.forCall fi.module [] f0.locals, hfi, hc, hty, ?_⟩
  have hres : Silmaril.Wasm.Abstract.CallRes.IndRes xStore (Frame.forCall fi.module [] f0.locals)
      ⟨0⟩ ⟨0⟩ .i32 0 (some 1) := by
    rw [hm]
    refine .func (ta := 0) (ti := (xStore.tables[0]?).getD ⟨⟨.i32, ⟨1, some 1⟩, .ref true .bot⟩, []⟩)
      rfl rfl ?_
    exact Silmaril.Wasm.Binaryen.DirectizeCast.refOk_cast hfi1 hy1 (PC.StoreOk.func_tyOk xStore_ok hfi1)
  exact .opOk (fun x h => by cases h) .nil rfl
    (.callIndOk (args := []) .nil hres hfi1 hty1 x_callee rfl .nil)

/-- **End to end, in Core 3.0.** Invoking function `0` of the instantiated store, whose body
makes an indirect call through the table, returns `42`, at every profile. This follows from
the closed extended semantics and the soundness of its closure on good stores. -/
theorem x_invoke (P : Numerics.Profile) :
    Steps P noHostX (invoke xStore 0 []) ⟨xStore, {}, vals [Val.i32 42]⟩ := by
  obtain ⟨fi, hfi, -, hty, -⟩ := fi0_spec
  have h := (oracleSoundX_closedX (P := P) (host := noHostX) xStore xStore {} 0 fi [] _ []
    (.normal [Val.i32 42]) (.callRefType fi.type) (storeChkE_of_storeChkEB xStore_chkEB) hfi hty rfl
    trivial ⟨xStore_good, x_caller⟩).2.1 _ rfl
  simp only [invoke, hfi, Option.map_some, Option.getD_some]
  simpa using h

end Silmaril.Proofs.Wasm.Interp.ExampleX
