module

public import Silmaril.Wasm.Interp.MemExample.Defs
public import Silmaril.Proofs.Wasm.Interp.Example

/-!
# A module with memory for native adequacy (proofs)

As for `Silmaril.Proofs.Wasm.Interp.Example`: validation, allocation, the
native-profile and arity checks, and native runs are computed by kernel
evaluation (`decide +kernel`). Typing comes from `prepare?_sound` and
`Instantiate.ok`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Interp.MemExample

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp Silmaril.Wasm.Interp.MemExample

theorem memMod_valid : ((Validation.validate? memMod).map fun mt => mt.imports.isEmpty) = some true :=
  by decide +kernel
theorem memPrep_some : (prepare? evalConst? ({} : Store Empty) memMod []).isSome = true :=
  by decide +kernel
theorem memPrep_shape : memPrep.1.code.isEmpty = true ∧ memPrep.2.isNone = true := by decide +kernel
theorem memStore_native : nativeFuncsB memStore.funcs = true := by decide +kernel
theorem memStore_chk : storeChkB memStore.funcs = true := by decide +kernel
theorem memStore_type (a : Nat) (ha : a < 2) :
    (memStore.funcs[a]?.bind fun fi => Validation.DefType.funcType? fi.type) =
      some ([.num (.int .i32)], [.num (.int .i32)]) := by
  rcases a with _ | _ | a
  · decide +kernel
  · decide +kernel
  · omega
theorem memRun_f : ((Binaryen.invokeRun 20 memStore 0 [Val.i32 7]).bind
    fun r => Binaryen.flowBeh r.2) = some .traps := by decide +kernel
theorem memRun_g : ((Binaryen.invokeRun 20 memStore 1 [Val.i32 0]).bind
    fun r => Binaryen.flowBeh r.2) = some .traps := by decide +kernel

theorem memPrep_eq : prepare? evalConst? ({} : Store Empty) memMod [] = some memPrep := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp memPrep_some
  simp [memPrep, hp]

theorem mem_instantiate (P : Numerics.Profile) (host : HostSemantics Empty) :
    Instantiate P host ({} : Store Empty) memMod [] memPrep.1 := by
  obtain ⟨mt, hmt, hnil⟩ : ∃ mt, Validation.validate? memMod = some mt ∧ mt.imports.isEmpty := by
    rcases h : Validation.validate? memMod with _ | mt
    · have hm := memMod_valid
      simp [h] at hm
    · have hm := memMod_valid
      simp only [h, Option.map_some, Option.some.injEq] at hm
      exact ⟨mt, rfl, hm⟩
  have himp : mt.imports = [] := List.isEmpty_iff.mp hnil
  have hvalid : ∃ xtE xtI, Validation.ModuleOk memMod ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk ({} : Store Empty)) [] xtI :=
    ⟨mt.exports, mt.imports, by simpa using Validation.validate?_sound hmt, by rw [himp]; exact .nil⟩
  have hst : memPrep.2 = none := Option.isNone_iff_eq_none.mp memPrep_shape.2
  have h : Instantiate P host ({} : Store Empty) memMod [] (memPrep.1.withStart memPrep.2) :=
    (prepare?_sound (P := P) (host := host) (c := memPrep.1) (st := memPrep.2) evalConst?_evalSound
      memPrep_eq hvalid).2
  have hw : memPrep.1.withStart memPrep.2 = memPrep.1 := by rw [hst]; rfl
  rwa [hw] at h

theorem memStore_ok : StoreOk memStore := by
  have hc : ConfigOk memPrep.1 [] :=
    Instantiate.ok SingleThreaded.divHost_ok Binaryen.storeOk_empty
      (mem_instantiate (SingleThreaded.profile fun _ _ _ _ => false) SingleThreaded.divHost)
  exact SingleThreaded.ConfigOk.storeOk hc

theorem mem_invokeOk (a : Nat) (ha : a < 2) (x : BitVec 32) : InvokeOk memStore a [Val.i32 x] := by
  obtain ⟨fi, hfi, hty⟩ : ∃ fi, memStore.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type = some ([.num (.int .i32)], [.num (.int .i32)]) := by
    have ht := memStore_type a ha
    rcases h : memStore.funcs[a]? with _ | fi
    · simp [h] at ht
    · exact ⟨fi, rfl, by simpa [h] using ht⟩
  unfold Validation.DefType.funcType? at hty
  split at hty
  · rename_i ps rs he
    simp only [Option.some.injEq, Prod.mk.injEq] at hty
    refine ⟨fi, ps, rs, hfi, Validation.Expand.iff.mpr he, ?_⟩
    rw [hty.1]
    exact .cons (ValOk.num _) .nil
  · cases hty

end Silmaril.Proofs.Wasm.Interp.MemExample
