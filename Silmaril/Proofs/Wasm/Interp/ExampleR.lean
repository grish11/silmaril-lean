module

public import Silmaril.Wasm.Interp.ExampleR.Defs
public import Silmaril.Proofs.Wasm.Interp.ExampleX
public import Silmaril.Proofs.Wasm.Interp.TypedCloseT

@[expose] public section

/-!
# A store whose function makes a reference call (proofs)
-/

namespace Silmaril.Proofs.Wasm.Interp.ExampleR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp Silmaril.Wasm.Interp.ExampleX
open Silmaril.Wasm.Interp.ExampleR
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.XRecursion
open Silmaril.Proofs.Wasm.Interp.ExampleX (storeChkE_of_storeChkEB)

theorem rMod_valid : ((Validation.validate? rMod).map fun mt => mt.imports.isEmpty) = some true :=
  by decide +kernel
theorem rPrep_some : (prepare? evalConst? ({} : Store Empty) rMod []).isSome = true :=
  by decide +kernel
theorem rPrep_shape : rPrep.1.code.isEmpty = true ∧ rPrep.2.isNone = true := by decide +kernel
theorem rStore_chkEB : storeChkEB irExt rStore.funcs = true := by decide +kernel
theorem rStore_not_chkB : storeChkB rStore.funcs = false := by decide +kernel

theorem rPrep_eq : prepare? evalConst? ({} : Store Empty) rMod [] = some rPrep := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp rPrep_some
  simp [rPrep, hp]

/-- **`rMod` instantiates to `rPrep.1`**, at every profile and host. -/
theorem r_instantiate (P : Numerics.Profile) (host : HostSemantics Empty) :
    Instantiate P host ({} : Store Empty) rMod [] rPrep.1 := by
  obtain ⟨mt, hmt, hnil⟩ : ∃ mt, Validation.validate? rMod = some mt ∧ mt.imports.isEmpty := by
    rcases h : Validation.validate? rMod with _ | mt
    · have hm := rMod_valid
      simp [h] at hm
    · have hm := rMod_valid
      simp only [h, Option.map_some, Option.some.injEq] at hm
      exact ⟨mt, rfl, hm⟩
  have himp : mt.imports = [] := List.isEmpty_iff.mp hnil
  have hvalid : ∃ xtE xtI, Validation.ModuleOk rMod ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk ({} : Store Empty)) [] xtI :=
    ⟨mt.exports, mt.imports, by simpa using Validation.validate?_sound hmt, by rw [himp]; exact .nil⟩
  have hst : rPrep.2 = none := Option.isNone_iff_eq_none.mp rPrep_shape.2
  have h : Instantiate P host ({} : Store Empty) rMod [] (rPrep.1.withStart rPrep.2) :=
    (prepare?_sound (P := P) (host := host) (c := rPrep.1) (st := rPrep.2) evalConst?_evalSound
      rPrep_eq hvalid).2
  have hw : rPrep.1.withStart rPrep.2 = rPrep.1 := by rw [hst]; rfl
  rwa [hw] at h

/-- **The store of the instance is typed.** -/
theorem rStore_ok : StoreOk rStore := by
  have hc : ConfigOk rPrep.1 [] :=
    Instantiate.ok SingleThreaded.divHost_ok Binaryen.storeOk_empty
      (r_instantiate (SingleThreaded.profile fun _ _ _ _ => false) SingleThreaded.divHost)
  exact SingleThreaded.ConfigOk.storeOk hc

theorem rStore_chkE : StoreChkE irExt rStore.funcs := storeChkE_of_storeChkEB rStore_chkEB

abbrev h0 : Func := ⟨⟨1⟩, [], [.localGet ⟨0⟩, .callRef ⟨0⟩]⟩
abbrev h1 : Func := ⟨⟨0⟩, [], [.intConst .i32 42]⟩

theorem fi1_spec : ∃ fi : FuncInst Empty, rStore.funcs[1]? = some fi ∧ fi.code = .wasm h1 ∧
    Validation.DefType.funcType? fi.type = some ([], [.num (.int .i32)]) :=
  ⟨_, rfl, rfl, rfl⟩

/-- The argument: a reference to function `1`. -/
abbrev arg : Val := .ref (.func 1)

/-- **The callee**: `42`. -/
theorem r_callee : closedCallX rStore 1 [] (rStore, .normal [Val.i32 42]) := by
  obtain ⟨fi, hfi, hc, hty⟩ := fi1_spec
  rw [closedCallX_fixpoint]
  refine ⟨fi, h1, [], [.num (.int .i32)], Frame.forCall fi.module [] h1.locals, hfi, hc, hty, ?_⟩
  exact .opOk (fun x h => by cases h) .nil rfl .nil

/-- **The caller**: `call_ref` on its argument `ref.func 1`. -/
theorem r_caller : closedCallX rStore 0 [arg] (rStore, .normal [Val.i32 42]) := by
  obtain ⟨fi1, hfi1, -, hty1⟩ := fi1_spec
  obtain ⟨fi, hfi, hc, hty⟩ : ∃ fi : FuncInst Empty, rStore.funcs[0]? = some fi ∧
      fi.code = .wasm h0 ∧ Validation.DefType.funcType? fi.type =
        some ([.refv (.ref true (.use (.dt fi1.type)))], [.num (.int .i32)]) := by
    obtain rfl : fi1 = _ := Option.some.inj hfi1.symm
    exact ⟨_, rfl, rfl, rfl⟩
  rw [closedCallX_fixpoint]
  refine ⟨fi, h0, _, [.num (.int .i32)], Frame.forCall fi.module [arg] h0.locals, hfi, hc, hty, ?_⟩
  exact .opOk (fun x h => by cases h) .nil rfl
    (.callRefOk (args := []) .nil hfi1 hty1 r_callee rfl .nil)

theorem funcType_of_expandR {d : Validation.DefType} {ps rs : Validation.Ty (.list .val)}
    (he : Validation.Expand d (.func ps rs)) :
    Validation.DefType.funcType? d = some (ps.toList, rs.toList) := by
  unfold Validation.DefType.funcType?
  rw [Validation.Expand.iff.mp he]

/-- The invocation is typed. -/
theorem r_invokeOk : InvokeOk rStore 0 [arg] := by
  obtain ⟨fi1, hfi1, -, -⟩ := fi1_spec
  obtain ⟨fi, hfi, hty⟩ : ∃ fi : FuncInst Empty, rStore.funcs[0]? = some fi ∧
      Validation.DefType.funcType? fi.type =
        some ([.refv (.ref true (.use (.dt fi1.type)))], [.num (.int .i32)]) := by
    obtain rfl : fi1 = _ := Option.some.inj hfi1.symm
    exact ⟨_, rfl, rfl⟩
  obtain ⟨ps, rs, he, -, -⟩ := expand_of_funcType hty
  have hps := funcType_of_expandR he
  rw [hty, Option.some.injEq, Prod.mk.injEq] at hps
  refine ⟨fi, ps, rs, hfi, he, ?_⟩
  rw [← hps.1]
  exact .cons (.ref (.sub (.func hfi1) (.ref (.use (.dt (PC.StoreOk.func_tyOk rStore_ok hfi1))))
    (.refNull .heapRefl))) .nil

/-- **End to end, in Core 3.0**: invoking function `0` on `ref.func 1`, whose body makes a
`call_ref`, returns `42`, at every profile. The call's arity premise is discharged from the
typing of the call site (typed closure, `oracleSoundX_typedClosed`). -/
theorem r_invoke (P : Numerics.Profile) :
    Steps P noHostX (invoke rStore 0 [arg]) ⟨rStore, {}, vals [Val.i32 42]⟩ := by
  obtain ⟨fi, ps, rs, hfi, he, hvs⟩ := r_invokeOk
  have hty := funcType_of_expandR he
  have hE := entry_of_invokeOk (P := P) rStore_ok r_invokeOk
  have h := (oracleSoundX_typedClosed (P := P) rStore rStore {} 0 fi ps.toList rs.toList [arg]
    (.normal [Val.i32 42]) (.callRefType fi.type) rStore_chkE hfi hty hvs.length_eq trivial
    ⟨hE, r_caller⟩).2.1 _ rfl
  have hrs : rs.toList.length = 1 := by
    obtain ⟨fi1, hfi1, -, -⟩ := fi1_spec
    obtain ⟨fi', hfi', hty'⟩ : ∃ fi : FuncInst Empty, rStore.funcs[0]? = some fi ∧
        Validation.DefType.funcType? fi.type =
          some ([.refv (.ref true (.use (.dt fi1.type)))], [.num (.int .i32)]) := by
      obtain rfl : fi1 = _ := Option.some.inj hfi1.symm
      exact ⟨_, rfl, rfl⟩
    rw [hfi] at hfi'; cases hfi'
    rw [hty, Option.some.injEq, Prod.mk.injEq] at hty'
    rw [hty'.2]; rfl
  simp only [invoke, hfi, Option.map_some, Option.getD_some]
  simpa [hrs] using h

theorem h0_not_ind : (rStore.funcs.all fun fi => match fi.code with
    | .wasm fn => indOkL fi.module (Binaryen.liftInstrs fn.body)
    | .host _ => true) = false := by decide +kernel

/-- **The store is outside the good-store closure**: its `call_ref` is excluded there. -/
theorem rStore_not_good : ¬ GoodStoreX rStore := by
  intro h
  have hall : (rStore.funcs.all fun fi => match fi.code with
      | .wasm fn => indOkL fi.module (Binaryen.liftInstrs fn.body)
      | .host _ => true) = true := by
    refine List.all_eq_true.mpr fun fi hfi => ?_
    obtain ⟨a, ha⟩ := List.getElem?_of_mem hfi
    split
    · rename_i fn hc
      exact (h.2 a fi fn ha hc).2
    · rfl
  rw [h0_not_ind] at hall
  cases hall

end Silmaril.Proofs.Wasm.Interp.ExampleR
