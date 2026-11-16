module

public import Silmaril.Wasm.Abstract.SelfLoop.Defs
public import Silmaril.Wasm.Abstract.Function.Defs
public import Silmaril.Wasm.Interp.Thms
public import Silmaril.Wasm.Binaryen.AdequacyModule
public import Silmaril.Wasm.SingleThreaded.Soundness
import Silmaril.Proofs.Wasm.Abstract.SelfLoop.Basic

/-!
# `(func (call 0))`: proofs

The validation, the allocation and the store of `recMod` are computed by
kernel evaluation of `validate?` and `prepare?`, as for
`Silmaril.Wasm.Interp.Example`. The same goes for the executable checks
`nativeFuncsB`, `storeChkB` and `selfLoopB`. Typing comes from
`prepare?_sound` and `Instantiate.ok`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.SelfLoop.Example

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp Silmaril.Wasm.Abstract

theorem recMod_valid : ((Validation.validate? recMod).map fun mt => mt.imports.isEmpty) = some true :=
  by decide +kernel
theorem recPrep_some : (prepare? evalConst? ({} : Store Empty) recMod []).isSome = true :=
  by decide +kernel
theorem recPrep_shape : recPrep.1.code.isEmpty = true ∧ recPrep.2.isNone = true := by decide +kernel
theorem recStore_native : nativeFuncsB recStore.funcs = true := by decide +kernel
theorem recStore_chk : storeChkB recStore.funcs = true := by decide +kernel
theorem recStore_selfLoopB : selfLoopB recStore 0 = true := by decide +kernel
theorem recStore_type : (recStore.funcs[0]?.bind fun fi => Validation.DefType.funcType? fi.type) =
    some ([], []) := by decide +kernel

theorem recPrep_eq : prepare? evalConst? ({} : Store Empty) recMod [] = some recPrep := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp recPrep_some
  simp [recPrep, hp]

/-- `recMod` instantiates to `recPrep.1`, at every profile and host. -/
theorem rec_instantiate (P : Numerics.Profile) (host : HostSemantics Empty) :
    Instantiate P host ({} : Store Empty) recMod [] recPrep.1 := by
  obtain ⟨mt, hmt, hnil⟩ : ∃ mt, Validation.validate? recMod = some mt ∧ mt.imports.isEmpty := by
    rcases h : Validation.validate? recMod with _ | mt
    · have hm := recMod_valid
      simp [h] at hm
    · have hm := recMod_valid
      simp only [h, Option.map_some, Option.some.injEq] at hm
      exact ⟨mt, rfl, hm⟩
  have himp : mt.imports = [] := List.isEmpty_iff.mp hnil
  have hvalid : ∃ xtE xtI, Validation.ModuleOk recMod ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk ({} : Store Empty)) [] xtI :=
    ⟨mt.exports, mt.imports, by simpa using Validation.validate?_sound hmt, by rw [himp]; exact .nil⟩
  have hst : recPrep.2 = none := Option.isNone_iff_eq_none.mp recPrep_shape.2
  have h : Instantiate P host ({} : Store Empty) recMod [] (recPrep.1.withStart recPrep.2) :=
    (prepare?_sound (P := P) (host := host) (c := recPrep.1) (st := recPrep.2) evalConst?_evalSound
      recPrep_eq hvalid).2
  have hw : recPrep.1.withStart recPrep.2 = recPrep.1 := by rw [hst]; rfl
  rwa [hw] at h

theorem recStore_ok : StoreOk recStore := by
  have hc : ConfigOk recPrep.1 [] :=
    Instantiate.ok SingleThreaded.divHost_ok Binaryen.storeOk_empty
      (rec_instantiate (SingleThreaded.profile fun _ _ _ _ => false) SingleThreaded.divHost)
  exact SingleThreaded.ConfigOk.storeOk hc

theorem rec_invokeOk : InvokeOk recStore 0 [] := by
  obtain ⟨fi, hfi, hty⟩ : ∃ fi, recStore.funcs[0]? = some fi ∧
      Validation.DefType.funcType? fi.type = some ([], []) := by
    rcases h : recStore.funcs[0]? with _ | fi
    · have ht := recStore_type
      simp [h] at ht
    · exact ⟨fi, rfl, by simpa [h] using recStore_type⟩
  unfold Validation.DefType.funcType? at hty
  split at hty
  · rename_i ps rs he
    simp only [Option.some.injEq, Prod.mk.injEq] at hty
    refine ⟨fi, ps, rs, hfi, Validation.Expand.iff.mpr he, ?_⟩
    rw [hty.1]
    exact .nil
  · cases hty

theorem rec_selfLoop : SelfLoop recStore 0 := selfLoop_of_selfLoopB recStore_selfLoopB

theorem rec_wasmFun (P : Numerics.Profile) :
    wasmFun P Binaryen.closedHost 0 recStore [] = {([], .div)} :=
  wasmFun_eq rec_selfLoop recStore_ok (nativeFuncsOk_of_check recStore_native)
    (storeChk_of_check recStore_chk) rec_invokeOk P

end Silmaril.Proofs.Wasm.Abstract.SelfLoop.Example
