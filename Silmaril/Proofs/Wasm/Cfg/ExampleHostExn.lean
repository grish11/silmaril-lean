module

public import Silmaril.Wasm.Cfg.ExampleHostExn.Defs
public import Silmaril.Wasm.Game.SpecInst.Thms
public import Silmaril.Wasm.Cfg.CfgValid.Thms
public import Silmaril.Wasm.Interp.ExampleX.Defs
public import Silmaril.Wasm.SingleThreaded.Soundness

@[expose] public section

/-!
# Host exceptions and traps under `try_table`, on the CFG closure: validation (proofs)

Validation, instantiation and the store checks by kernel evaluation (`decide +kernel`, on Boolean
summaries); `hxI` is a spec instance of `hxMod` against a fresh host function
(`Game.IsSpecInstance`), so its configuration is typed (`IsSpecInstance.ok`) and its store is
valid (`StoreOk`). The exception checker accepts the store (`storeChkEB`), the hypothesis the
`CfgValid` theorems keep.
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleHostExn

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Validation
  Silmaril.Wasm.Cfg.ExampleHostExn
open Silmaril.Wasm.Interp (StoreChkE ehExt)
open Silmaril.Wasm.Interp.ExampleX (storeChkEB funcChkEB)

theorem hx_valid_some : (validate? hxMod).isSome = true := by decide +kernel
theorem hx_prep_some : (prepare? evalConst? (importStore (CExternType.funcs hxMT.imports)) hxMod
    (importAddrs hxMT)).isSome = true := by decide +kernel
theorem hx_imports_func : hxMT.imports.all (fun xt => match xt with
    | .func _ => true | _ => false) = true := by decide +kernel
theorem hx_impT : (CExternType.funcs hxMT.imports).map FnType.ofDefType? =
    [some ⟨[], [.num (.int .i32)]⟩] := by decide +kernel
theorem hx_addrs : exportFuncAddrs hxPrep.1.frame.module = [1, 2, 3] := by decide +kernel
theorem hx_expT : [1, 2, 3].map (fun a => (hxStore.funcs[a]?).bind
    fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) =
    [some ⟨[], [.num (.int .i32)]⟩, some ⟨[], [.num (.int .i32)]⟩, some ⟨[], []⟩] := by
  decide +kernel
theorem hx_start : hxPrep.2.isNone = true := by decide +kernel
theorem hx_chkB : storeChkEB (ehExt hxStore.tags) hxStore.funcs = true := by decide +kernel

/-- The validated type. -/
theorem hx_valid : validate? hxMod = some hxMT := by
  obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp hx_valid_some
  show validate? hxMod = some ((validate? hxMod).getD _)
  rw [hmt]
  rfl

/-- The allocation. -/
theorem hx_prep : prepare? evalConst? (importStore (CExternType.funcs hxMT.imports)) hxMod
    (importAddrs hxMT) = some hxPrep := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hx_prep_some
  show _ = some ((prepare? evalConst? (importStore (CExternType.funcs hxMT.imports)) hxMod
    (importAddrs hxMT)).getD _)
  rw [hq]
  rfl

theorem hx_importTypes : List.Forall₂ (fun d ft => FnType.ofDefType? d = some ft)
    (CExternType.funcs hxMT.imports) hxI.imports := by
  have hl : ((CExternType.funcs hxMT.imports).map FnType.ofDefType?).length = 1 := by
    rw [hx_impT]; rfl
  obtain ⟨d, hd⟩ := List.length_eq_one_iff.mp (by simpa using hl)
  have h' : [d].map FnType.ofDefType? = [some ⟨[], [.num (.int .i32)]⟩] := hd ▸ hx_impT
  rw [hd]
  exact .cons (List.cons.inj h').1 .nil

theorem hx_exportTypes : List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat,
      hxI.store.funcs[a]? = some fi ∧ FnType.ofDefType? fi.type = some ft)
    hxI.addrs hxI.exports := by
  have ha : hxI.addrs = [1, 2, 3] := hx_addrs
  rw [ha]
  have h := hx_expT
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
  obtain ⟨h1, h2, h3, -⟩ := h
  have key : ∀ (a : Nat) ft, (hxStore.funcs[a]?).bind (fun (fi : FuncInst Nat) =>
      FnType.ofDefType? fi.type) = some ft →
      ∃ fi : FuncInst Nat, hxI.store.funcs[a]? = some fi ∧ FnType.ofDefType? fi.type = some ft :=
    fun a ft h => Option.bind_eq_some_iff.mp h
  exact .cons (key _ _ h1) (.cons (key _ _ h2) (.cons (key _ _ h3) .nil))

/-- **`hxI` is the spec instance of `hxMod` against a fresh host function.** -/
theorem hx_specInstance : IsSpecInstance hxMod hxMT hxI hxC₀ where
  valid := hx_valid
  funcImports xt hxt := by
    have h := List.all_eq_true.mp hx_imports_func xt hxt
    cases xt with
    | func d => exact ⟨d, rfl⟩
    | _ => cases h
  importTypes := hx_importTypes
  prepared := ⟨hxPrep.1, hxPrep.2, hx_prep, rfl, rfl, rfl⟩
  exportTypes := hx_exportTypes

/-- **The store of the instance is valid.** -/
theorem hx_storeOk : StoreOk hxStore := by
  have h := hx_specInstance.ok.1
  have hs : hxC₀.store = hxStore := hx_specInstance.store_eq
  rw [← hs]
  exact SingleThreaded.ConfigOk.storeOk h

/-- **The exception checker accepts the store.** -/
theorem hx_chk : StoreChkE (ehExt hxStore.tags) hxStore.funcs := by
  intro a fi fn ps rs hfi hcode hty
  have hb : funcChkEB (ehExt hxStore.tags) hxStore.funcs fi = true :=
    List.all_eq_true.mp hx_chkB fi (List.mem_of_getElem? hfi)
  simpa only [funcChkEB, hcode, hty] using hb

end Silmaril.Wasm.Cfg.Proofs.ExampleHostExn
