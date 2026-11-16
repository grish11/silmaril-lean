module

public import Silmaril.Wasm.Interp.ExampleT.Defs
public import Silmaril.Proofs.Wasm.Interp.ExampleX

@[expose] public section

/-!
# A store whose functions make tail calls (proofs)

As `ExampleX`: validation, allocation and the executable checks by kernel evaluation
(`decide +kernel`), the store's typing from `prepare?_sound` and `Instantiate.ok`, the closed
extended runs by hand, and their Core 3.0 behaviour from the closure's soundness for the tail
checker (`oracleSoundT_closedX`).
-/

namespace Silmaril.Proofs.Wasm.Interp.ExampleT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp Silmaril.Wasm.Interp.ExampleX
open Silmaril.Wasm.Interp.ExampleT
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.XRecursion
open Silmaril.Proofs.Wasm.Interp.ExampleX (storeChkE_of_storeChkEB tyTypes_of_storeOk)

theorem tMod_valid : ((Validation.validate? tMod).map fun mt => mt.imports.isEmpty) = some true :=
  by decide +kernel
theorem tPrep_some : (prepare? evalConst? ({} : Store Empty) tMod []).isSome = true :=
  by decide +kernel
theorem tPrep_shape : tPrep.1.code.isEmpty = true ∧ tPrep.2.isNone = true := by decide +kernel
/-- **The tail store check passes**: the store's functions with tail calls are checked by
`tExt`. -/
theorem tStore_chkEB : storeChkEB tExt tStore.funcs = true := by decide +kernel
/-- Neither the native nor the `irExt` store check passes: the tail forms are outside both. -/
theorem tStore_not_chkB : storeChkB tStore.funcs = false := by decide +kernel
theorem tStore_not_irB : storeChkEB irExt tStore.funcs = false := by decide +kernel
theorem tStore_indB : (tStore.funcs.all fun fi => match fi.code with
    | .wasm fn => indOkL fi.module (Binaryen.liftInstrs fn.body)
    | .host _ => true) = true := by decide +kernel

theorem tPrep_eq : prepare? evalConst? ({} : Store Empty) tMod [] = some tPrep := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp tPrep_some
  simp [tPrep, hp]

/-- **`tMod` instantiates to `tPrep.1`**, at every profile and host. -/
theorem t_instantiate (P : Numerics.Profile) (host : HostSemantics Empty) :
    Instantiate P host ({} : Store Empty) tMod [] tPrep.1 := by
  obtain ⟨mt, hmt, hnil⟩ : ∃ mt, Validation.validate? tMod = some mt ∧ mt.imports.isEmpty := by
    rcases h : Validation.validate? tMod with _ | mt
    · have hm := tMod_valid
      simp [h] at hm
    · have hm := tMod_valid
      simp only [h, Option.map_some, Option.some.injEq] at hm
      exact ⟨mt, rfl, hm⟩
  have himp : mt.imports = [] := List.isEmpty_iff.mp hnil
  have hvalid : ∃ xtE xtI, Validation.ModuleOk tMod ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk ({} : Store Empty)) [] xtI :=
    ⟨mt.exports, mt.imports, by simpa using Validation.validate?_sound hmt, by rw [himp]; exact .nil⟩
  have hst : tPrep.2 = none := Option.isNone_iff_eq_none.mp tPrep_shape.2
  have h : Instantiate P host ({} : Store Empty) tMod [] (tPrep.1.withStart tPrep.2) :=
    (prepare?_sound (P := P) (host := host) (c := tPrep.1) (st := tPrep.2) evalConst?_evalSound
      tPrep_eq hvalid).2
  have hw : tPrep.1.withStart tPrep.2 = tPrep.1 := by rw [hst]; rfl
  rwa [hw] at h

/-- **The store of the instance is typed.** -/
theorem tStore_ok : StoreOk tStore := by
  have hc : ConfigOk tPrep.1 [] :=
    Instantiate.ok SingleThreaded.divHost_ok Binaryen.storeOk_empty
      (t_instantiate (SingleThreaded.profile fun _ _ _ _ => false) SingleThreaded.divHost)
  exact SingleThreaded.ConfigOk.storeOk hc

/-- **The store is good** for the closure's soundness. -/
theorem tStore_good : GoodStoreX tStore := by
  refine ⟨fun a fi hfi => PC.StoreOk.func_tyOk tStore_ok hfi, fun a fi fn hfi hc => ?_⟩
  refine ⟨tyTypes_of_storeOk tStore_ok hfi hc, ?_⟩
  have hb := List.all_eq_true.mp tStore_indB fi (List.mem_of_getElem? hfi)
  simpa only [hc] using hb

theorem tStore_chkE : StoreChkE tExt tStore.funcs := storeChkE_of_storeChkEB tStore_chkEB

/-- The instance of the functions. -/
abbrev tMI : ModuleInst := (tStore.funcs[0]?.map (·.module)).getD {}

abbrev g0 : Func := ⟨⟨0⟩, [], [.intConst .i32 0, .returnCallIndirect ⟨0⟩ ⟨0⟩]⟩
abbrev g1 : Func := ⟨⟨0⟩, [], [.intConst .i32 42]⟩
abbrev g2 : Func := ⟨⟨0⟩, [], [.intConst .i32 0, .returnCallIndirect ⟨1⟩ ⟨0⟩]⟩
abbrev g3 : Func := ⟨⟨0⟩, [], [.returnCall ⟨1⟩]⟩

theorem gi_spec (a : Nat) (g : Func) (h : a = 0 ∧ g = g0 ∨ a = 1 ∧ g = g1 ∨ a = 2 ∧ g = g2 ∨
    a = 3 ∧ g = g3) : ∃ fi : FuncInst Empty, tStore.funcs[a]? = some fi ∧ fi.code = .wasm g ∧
    Validation.DefType.funcType? fi.type = some ([], [.num (.int .i32)]) ∧ fi.module = tMI ∧
    tMI.types[0]? = some fi.type := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- **The callee**: `42`. -/
theorem t_callee : closedCallX tStore 1 [] (tStore, .normal [Val.i32 42]) := by
  obtain ⟨fi, hfi, hc, hty, -, -⟩ := gi_spec 1 g1 (by simp)
  rw [closedCallX_fixpoint]
  refine ⟨fi, g1, [], [.num (.int .i32)], Frame.forCall fi.module [] g1.locals, hfi, hc, hty, ?_⟩
  exact .opOk (fun x h => by cases h) .nil rfl .nil

/-- **A resolved indirect tail call**: function `0` tail-calls table `0`'s slot `0`, function
`1`, and returns its `42`. -/
theorem t_indirect : closedCallX tStore 0 [] (tStore, .ret [Val.i32 42]) := by
  obtain ⟨fi1, hfi1, -, hty1, -, hy1⟩ := gi_spec 1 g1 (by simp)
  obtain ⟨fi, hfi, hc, hty, hm, -⟩ := gi_spec 0 g0 (by simp)
  rw [closedCallX_fixpoint]
  refine ⟨fi, g0, [], [.num (.int .i32)], Frame.forCall fi.module [] g0.locals, hfi, hc, hty, ?_⟩
  have hres : Silmaril.Wasm.Abstract.CallRes.IndRes tStore (Frame.forCall fi.module [] g0.locals)
      ⟨0⟩ ⟨0⟩ .i32 0 (some 1) := by
    rw [hm]
    refine .func (ta := 0) (ti := (tStore.tables[0]?).getD ⟨⟨.i32, ⟨1, some 1⟩, .ref true .bot⟩, []⟩)
      rfl rfl ?_
    exact Silmaril.Wasm.Binaryen.DirectizeCast.refOk_cast hfi1 hy1 (PC.StoreOk.func_tyOk tStore_ok hfi1)
  exact .opOk (fun x h => by cases h) .nil rfl
    (.tail (args := []) .nil (.indirect hres) hfi1 hty1 t_callee (.inl ⟨_, rfl⟩))

/-- **A null tail call**: function `2` tail-calls through table `1`'s null slot, a trap. -/
theorem t_null : closedCallX tStore 2 [] (tStore, .trap) := by
  obtain ⟨fi, hfi, hc, hty, hm, hy⟩ := gi_spec 2 g2 (by simp)
  rw [closedCallX_fixpoint]
  refine ⟨fi, g2, [], [.num (.int .i32)], Frame.forCall fi.module [] g2.locals, hfi, hc, hty, ?_⟩
  have hres : Silmaril.Wasm.Abstract.CallRes.IndRes tStore (Frame.forCall fi.module [] g2.locals)
      ⟨1⟩ ⟨0⟩ .i32 0 none := by
    rw [hm]
    refine .null (ta := 1) (ti := (tStore.tables[1]?).getD ⟨⟨.i32, ⟨1, some 1⟩, .ref true .bot⟩, []⟩)
      rfl rfl ?_
    show RefOk tStore .null (tMI.instRef ⟨true, .typeIdx ⟨0⟩⟩)
    rw [Silmaril.Wasm.Binaryen.DirectizeCast.instRef_typeIdx hy]
    exact .sub .null (.ref (.use (.dt (PC.StoreOk.func_tyOk tStore_ok hfi)))) (.refNull .bot)
  exact .opOk (fun x h => by cases h) .nil rfl (.tailRes (args := []) .nil (.indirectTrap hres))

/-- **A direct tail call**: function `3` tail-calls function `1` and returns its `42`. -/
theorem t_direct : closedCallX tStore 3 [] (tStore, .ret [Val.i32 42]) := by
  obtain ⟨fi, hfi, hc, hty, hm, -⟩ := gi_spec 3 g3 (by simp)
  obtain ⟨fi1, hfun⟩ : ∃ fi1, tStore.func? (Frame.forCall tMI [] g3.locals) ⟨1⟩ = some (1, fi1) :=
    ⟨_, rfl⟩
  obtain ⟨fi1', hfi1, -, hty1, -, -⟩ := gi_spec 1 g1 (by simp)
  obtain rfl : fi1 = fi1' := Option.some.inj ((funcs_of_func? hfun).symm.trans hfi1)
  rw [closedCallX_fixpoint]
  refine ⟨fi, g3, [], [.num (.int .i32)], Frame.forCall fi.module [] g3.locals, hfi, hc, hty, ?_⟩
  rw [hm]
  exact .tail (args := []) .nil (.direct hfun) hfi1 hty1 t_callee (.inl ⟨_, rfl⟩)

theorem t_invoke_of {a : Nat} {fl : Binaryen.Flow} (P : Numerics.Profile) (g : Func)
    (hg : a = 0 ∧ g = g0 ∨ a = 1 ∧ g = g1 ∨ a = 2 ∧ g = g2 ∨ a = 3 ∧ g = g3)
    (hcl : closedCallX tStore a [] (tStore, fl)) :
    (∀ vs, fl.retVals = some vs →
      Steps P noHostX (invoke tStore a []) ⟨tStore, {}, vals (vs.take 1).reverse⟩) ∧
    (fl = .trap → Steps P noHostX (invoke tStore a []) ⟨tStore, {}, [.trap]⟩) := by
  obtain ⟨fi, hfi, -, hty, -, -⟩ := gi_spec a g hg
  have h := (oracleSoundT_closedX (P := P) (host := noHostX) tStore tStore {} a fi [] _ []
    fl (.callRefType fi.type) tStore_chkE hfi hty rfl trivial ⟨tStore_good, hcl⟩).2
  simp only [invoke, hfi, Option.map_some, Option.getD_some]
  simpa using h

/-- **End to end, a resolved indirect tail call**: invoking function `0` returns `42`. -/
theorem t_invoke (P : Numerics.Profile) :
    Steps P noHostX (invoke tStore 0 []) ⟨tStore, {}, vals [Val.i32 42]⟩ :=
  (t_invoke_of P g0 (by simp) t_indirect).1 _ rfl

/-- **End to end, a null tail call**: invoking function `2` traps (in Core 3.0, once the
frame is left). -/
theorem t_invoke_null (P : Numerics.Profile) :
    Steps P noHostX (invoke tStore 2 []) ⟨tStore, {}, [.trap]⟩ :=
  (t_invoke_of P g2 (by simp) t_null).2 rfl

/-- **End to end, a direct tail call**: invoking function `3` returns `42`. -/
theorem t_invoke_direct (P : Numerics.Profile) :
    Steps P noHostX (invoke tStore 3 []) ⟨tStore, {}, vals [Val.i32 42]⟩ :=
  (t_invoke_of P g3 (by simp) t_direct).1 _ rfl

end Silmaril.Proofs.Wasm.Interp.ExampleT
