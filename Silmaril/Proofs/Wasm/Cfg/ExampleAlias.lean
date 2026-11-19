module

public import Silmaril.Wasm.Cfg.ExampleAlias.Defs
public import Silmaril.Wasm.Game.SpecInst.Thms
public import Silmaril.Wasm.Cfg.CfgInst.Thms
public import Silmaril.Wasm.Cfg.DanglingTyped.Thms
public import Silmaril.Wasm.Interp.ExampleX.Defs
public import Silmaril.Wasm.Interp.CheckComplete.Thms
public import Silmaril.Wasm.SingleThreaded.Soundness

@[expose] public section

/-!
# A validated aliasing cycle through a dangling host exception: validation (proofs)

Validation, instantiation and the store checks of `alMod` and `dcMod` by kernel evaluation
(`decide +kernel`, on Boolean summaries), as in `ExampleHostExn`. Both are spec instances
(`Game.IsSpecInstance`), so their stores are `StoreOk` and their instances well formed; the
exception checker accepts both stores (`storeChkEB`). `alStore` is in the checker's instruction
profile (`storeSupportedB`), so it has supported functions; `dcStore` is not, and its dead
`ref.test` breaks `FuncsSupp`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleAlias

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Validation
  Silmaril.Wasm.Cfg.ExampleAlias
open Silmaril.Wasm.Interp (StoreChkE ehExt)
open Silmaril.Wasm.Interp.ExampleX (storeChkEB funcChkEB)
open Silmaril.Wasm.Cfg.DanglingTyped (FuncsSupp ISupp Unsupp Structured)

/-! ## `alMod` -/

theorem al_valid_some : (validate? alMod).isSome = true := by decide +kernel
theorem al_prep_some : (prepare? evalConst? (importStore (CExternType.funcs alMT.imports)) alMod
    (importAddrs alMT)).isSome = true := by decide +kernel
theorem al_imports_func : alMT.imports.all (fun xt => match xt with
    | .func _ => true | _ => false) = true := by decide +kernel
theorem al_impT : (CExternType.funcs alMT.imports).map FnType.ofDefType? = [some ⟨[], []⟩] := by
  decide +kernel
theorem al_addrs : exportFuncAddrs alPrep.1.frame.module = [1] := by decide +kernel
theorem al_expT : [1].map (fun a => (alStore.funcs[a]?).bind
    fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) = [some ⟨[], []⟩] := by
  decide +kernel
theorem al_chkB : storeChkEB (ehExt alStore.tags) alStore.funcs = true := by decide +kernel
theorem al_supB : Interp.CheckComplete.storeSupportedB alStore.funcs = true := by decide +kernel

theorem al_valid : validate? alMod = some alMT := by
  obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp al_valid_some
  show validate? alMod = some ((validate? alMod).getD _)
  rw [hmt]
  rfl

theorem al_prep : prepare? evalConst? (importStore (CExternType.funcs alMT.imports)) alMod
    (importAddrs alMT) = some alPrep := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp al_prep_some
  show _ = some ((prepare? evalConst? (importStore (CExternType.funcs alMT.imports)) alMod
    (importAddrs alMT)).getD _)
  rw [hq]
  rfl

theorem al_importTypes : List.Forall₂ (fun d ft => FnType.ofDefType? d = some ft)
    (CExternType.funcs alMT.imports) alI.imports := by
  have hl : ((CExternType.funcs alMT.imports).map FnType.ofDefType?).length = 1 := by
    rw [al_impT]; rfl
  obtain ⟨d, hd⟩ := List.length_eq_one_iff.mp (by simpa using hl)
  have h' : [d].map FnType.ofDefType? = [some ⟨[], []⟩] := hd ▸ al_impT
  rw [hd]
  exact .cons (List.cons.inj h').1 .nil

theorem al_exportTypes : List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat,
      alI.store.funcs[a]? = some fi ∧ FnType.ofDefType? fi.type = some ft)
    alI.addrs alI.exports := by
  have ha : alI.addrs = [1] := al_addrs
  rw [ha]
  have h := al_expT
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
  exact .cons (Option.bind_eq_some_iff.mp h.1) .nil

/-- **`alI` is the spec instance of `alMod` against a fresh host function.** -/
theorem al_specInstance : IsSpecInstance alMod alMT alI alC₀ where
  valid := al_valid
  funcImports xt hxt := by
    have h := List.all_eq_true.mp al_imports_func xt hxt
    cases xt with
    | func d => exact ⟨d, rfl⟩
    | _ => cases h
  importTypes := al_importTypes
  prepared := ⟨alPrep.1, alPrep.2, al_prep, rfl, rfl, rfl⟩
  exportTypes := al_exportTypes

theorem al_storeOk : StoreOk alStore := by
  have h := al_specInstance.ok.1
  have hs : alC₀.store = alStore := al_specInstance.store_eq
  rw [← hs]
  exact SingleThreaded.ConfigOk.storeOk h

theorem al_wf : alI.WellFormed alStore := by
  have h := al_specInstance.ok.2
  rwa [al_specInstance.store_eq] at h

theorem al_chk : StoreChkE (ehExt alStore.tags) alStore.funcs := by
  intro a fi fn ps rs hfi hcode hty
  have hb : funcChkEB (ehExt alStore.tags) alStore.funcs fi = true :=
    List.all_eq_true.mp al_chkB fi (List.mem_of_getElem? hfi)
  simpa only [funcChkEB, hcode, hty] using hb

theorem al_supported : Interp.CheckComplete.StoreSupported alStore.funcs :=
  Interp.CheckComplete.storeSupportedB_iff.1 al_supB

theorem al_instDom : CfgInst.InstDom alI alStore := ⟨al_wf, al_chk⟩

theorem al_funcsSupp : FuncsSupp alStore :=
  DanglingTyped.funcsSupp_of_storeSupported al_storeOk al_supported

/-! ## `dcMod` -/

theorem dc_valid_some : (validate? dcMod).isSome = true := by decide +kernel
theorem dc_prep_some : (prepare? evalConst? (importStore (CExternType.funcs dcMT.imports)) dcMod
    (importAddrs dcMT)).isSome = true := by decide +kernel
theorem dc_imports_nil : dcMT.imports = [] := by decide +kernel
theorem dc_addrs : exportFuncAddrs dcPrep.1.frame.module = [0] := by decide +kernel
theorem dc_expT : [0].map (fun a => (dcStore.funcs[a]?).bind
    fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) = [some ⟨[], []⟩] := by
  decide +kernel
theorem dc_chkB : storeChkEB (ehExt dcStore.tags) dcStore.funcs = true := by decide +kernel
theorem dc_supB : Interp.CheckComplete.storeSupportedB dcStore.funcs = false := by decide +kernel
theorem dc_f0 : ∃ fi : FuncInst Nat, dcStore.funcs[0]? = some fi ∧
    fi.code = .wasm ⟨⟨0⟩, [], deadBody⟩ := ⟨_, rfl, rfl⟩

theorem dc_valid : validate? dcMod = some dcMT := by
  obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp dc_valid_some
  show validate? dcMod = some ((validate? dcMod).getD _)
  rw [hmt]
  rfl

theorem dc_prep : prepare? evalConst? (importStore (CExternType.funcs dcMT.imports)) dcMod
    (importAddrs dcMT) = some dcPrep := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp dc_prep_some
  show _ = some ((prepare? evalConst? (importStore (CExternType.funcs dcMT.imports)) dcMod
    (importAddrs dcMT)).getD _)
  rw [hq]
  rfl

theorem dc_exportTypes : List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat,
      dcI.store.funcs[a]? = some fi ∧ FnType.ofDefType? fi.type = some ft)
    dcI.addrs dcI.exports := by
  have ha : dcI.addrs = [0] := dc_addrs
  rw [ha]
  have h := dc_expT
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
  exact .cons (Option.bind_eq_some_iff.mp h.1) .nil

/-- **`dcI` is the spec instance of `dcMod`.** -/
theorem dc_specInstance : IsSpecInstance dcMod dcMT dcI dcC₀ where
  valid := dc_valid
  funcImports xt hxt := by rw [dc_imports_nil] at hxt; cases hxt
  importTypes := by rw [dc_imports_nil]; exact .nil
  prepared := ⟨dcPrep.1, dcPrep.2, dc_prep, rfl, rfl, rfl⟩
  exportTypes := dc_exportTypes

theorem dc_wf : dcI.WellFormed dcStore := by
  have h := dc_specInstance.ok.2
  rwa [dc_specInstance.store_eq] at h

theorem dc_chk : StoreChkE (ehExt dcStore.tags) dcStore.funcs := by
  intro a fi fn ps rs hfi hcode hty
  have hb : funcChkEB (ehExt dcStore.tags) dcStore.funcs fi = true :=
    List.all_eq_true.mp dc_chkB fi (List.mem_of_getElem? hfi)
  simpa only [funcChkEB, hcode, hty] using hb

/-- **`dcStore` is in the explicit domain** (well formed, accepted by the exception checker). -/
theorem dc_instDom : CfgInst.InstDom dcI dcStore := ⟨dc_wf, dc_chk⟩

theorem not_isupp_refTest (rt : RefType) : ¬ ISupp (.refTest rt) := by
  intro h
  cases h with
  | atom _ hn => exact hn trivial

/-- **`dcStore` does not have supported functions**: its dead `ref.test`. -/
theorem dc_not_funcsSupp : ¬ FuncsSupp dcStore := by
  intro h
  obtain ⟨fi, hfi, hc⟩ := dc_f0
  exact not_isupp_refTest ⟨true, .abstract .any⟩
    ((h fi (List.mem_of_getElem? hfi) _ hc).2 _ (by simp [deadBody]))

/-- `dcStore` is not in the checker's instruction profile. -/
theorem dc_not_supported : ¬ Interp.CheckComplete.StoreSupported dcStore.funcs := by
  rw [← Interp.CheckComplete.storeSupportedB_iff, dc_supB]; simp

end Silmaril.Wasm.Cfg.Proofs.ExampleAlias
