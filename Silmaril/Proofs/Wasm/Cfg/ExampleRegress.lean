module

public import Silmaril.Wasm.Cfg.ExampleRegress.Defs
public import Silmaril.Wasm.Game.SpecInst.Thms
public import Silmaril.Wasm.Cfg.CfgValid.Thms
public import Silmaril.Wasm.Interp.ExampleX.Defs
public import Silmaril.Wasm.SingleThreaded.Soundness

@[expose] public section

/-!
# Regression fixtures for the self-contained CFG closure: validation (proofs)

Validation, instantiation and the store checks by kernel evaluation (`decide +kernel`, on Boolean
summaries); `rgI` is a spec instance of `rgMod` against a fresh host function
(`Game.IsSpecInstance`), so its configuration is typed (`IsSpecInstance.ok`) and its store is
valid (`StoreOk`). The exception checker accepts the store (`storeChkEB`), the hypothesis the
`CfgValid` theorems keep.
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleRegress

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Validation
  Silmaril.Wasm.Cfg.ExampleRegress
open Silmaril.Wasm.Interp (StoreChkE ehExt)
open Silmaril.Wasm.Interp.ExampleX (storeChkEB funcChkEB)

theorem rg_valid_some : (validate? rgMod).isSome = true := by decide +kernel
theorem rg_prep_some : (prepare? evalConst? (importStore (CExternType.funcs rgMT.imports)) rgMod
    (importAddrs rgMT)).isSome = true := by decide +kernel
theorem rg_imports_func : rgMT.imports.all (fun xt => match xt with
    | .func _ => true | _ => false) = true := by decide +kernel
theorem rg_impT : (CExternType.funcs rgMT.imports).map FnType.ofDefType? =
    [some ⟨[.num (.int .i32)], []⟩] := by decide +kernel
theorem rg_addrs : exportFuncAddrs rgPrep.1.frame.module = [1, 2, 3, 4] := by decide +kernel
theorem rg_expT : [1, 2, 3, 4].map (fun a => (rgStore.funcs[a]?).bind
    fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) =
    [some ⟨[.num (.int .i32)], []⟩, some ⟨[], []⟩, some ⟨[], [.num (.int .i32)]⟩,
      some ⟨[], []⟩] := by decide +kernel
theorem rg_start : rgPrep.2.isNone = true := by decide +kernel
theorem rg_chkB : storeChkEB (ehExt rgStore.tags) rgStore.funcs = true := by decide +kernel

/-- The validated type. -/
theorem rg_valid : validate? rgMod = some rgMT := by
  obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp rg_valid_some
  show validate? rgMod = some ((validate? rgMod).getD _)
  rw [hmt]
  rfl

/-- The allocation. -/
theorem rg_prep : prepare? evalConst? (importStore (CExternType.funcs rgMT.imports)) rgMod
    (importAddrs rgMT) = some rgPrep := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rg_prep_some
  show _ = some ((prepare? evalConst? (importStore (CExternType.funcs rgMT.imports)) rgMod
    (importAddrs rgMT)).getD _)
  rw [hq]
  rfl

theorem rg_importTypes : List.Forall₂ (fun d ft => FnType.ofDefType? d = some ft)
    (CExternType.funcs rgMT.imports) rgI.imports := by
  have hl : ((CExternType.funcs rgMT.imports).map FnType.ofDefType?).length = 1 := by
    rw [rg_impT]; rfl
  obtain ⟨d, hd⟩ := List.length_eq_one_iff.mp (by simpa using hl)
  have h' : [d].map FnType.ofDefType? = [some ⟨[.num (.int .i32)], []⟩] := hd ▸ rg_impT
  rw [hd]
  exact .cons (List.cons.inj h').1 .nil

theorem rg_exportTypes : List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat,
      rgI.store.funcs[a]? = some fi ∧ FnType.ofDefType? fi.type = some ft)
    rgI.addrs rgI.exports := by
  have ha : rgI.addrs = [1, 2, 3, 4] := rg_addrs
  rw [ha]
  have h := rg_expT
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  have key : ∀ (a : Nat) ft, (rgStore.funcs[a]?).bind (fun (fi : FuncInst Nat) =>
      FnType.ofDefType? fi.type) = some ft →
      ∃ fi : FuncInst Nat, rgI.store.funcs[a]? = some fi ∧ FnType.ofDefType? fi.type = some ft :=
    fun a ft h => Option.bind_eq_some_iff.mp h
  exact .cons (key _ _ h1) (.cons (key _ _ h2) (.cons (key _ _ h3) (.cons (key _ _ h4) .nil)))

/-- **`rgI` is the spec instance of `rgMod` against a fresh host function.** -/
theorem rg_specInstance : IsSpecInstance rgMod rgMT rgI rgC₀ where
  valid := rg_valid
  funcImports xt hxt := by
    have h := List.all_eq_true.mp rg_imports_func xt hxt
    cases xt with
    | func d => exact ⟨d, rfl⟩
    | _ => cases h
  importTypes := rg_importTypes
  prepared := ⟨rgPrep.1, rgPrep.2, rg_prep, rfl, rfl, rfl⟩
  exportTypes := rg_exportTypes

/-- **The store of the instance is valid.** -/
theorem rg_storeOk : StoreOk rgStore := by
  have h := rg_specInstance.ok.1
  have hs : rgC₀.store = rgStore := rg_specInstance.store_eq
  rw [← hs]
  exact SingleThreaded.ConfigOk.storeOk h

/-- **The exception checker accepts the store.** -/
theorem rg_chk : StoreChkE (ehExt rgStore.tags) rgStore.funcs := by
  intro a fi fn ps rs hfi hcode hty
  have hb : funcChkEB (ehExt rgStore.tags) rgStore.funcs fi = true :=
    List.all_eq_true.mp rg_chkB fi (List.mem_of_getElem? hfi)
  simpa only [funcChkEB, hcode, hty] using hb

end Silmaril.Wasm.Cfg.Proofs.ExampleRegress
