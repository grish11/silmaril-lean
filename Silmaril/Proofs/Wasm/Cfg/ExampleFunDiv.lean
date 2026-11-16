module

public import Silmaril.Wasm.Cfg.ExampleFunDiv.Defs
public import Silmaril.Wasm.Cfg.FunctionCfg.Thms
public import Silmaril.Wasm.Interp.ExampleX.Thms
public import Silmaril.Wasm.Abstract.XDiverge.Thms
public import Silmaril.Wasm.Binaryen.Pass.DirectizeCast
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Proofs.Wasm.Cfg.RegionTail

@[expose] public section

/-!
# Function-level divergence through every call form: regression fixtures (proofs)

Validation, allocation and the executable checks by kernel evaluation, the store's typing from
`prepare?_sound` and `Instantiate.ok`. Native extended divergence of functions `0`, `1`, `2` by
coinduction on `XDiverge.EvalDivX` (each body reaches its own call: `callIndCallee`,
`callRefCallee`, `tailCallee`); closed trap outcomes of functions `3`, `4`, which exclude it.
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleFunDiv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp Silmaril.Wasm.Cfg.ExampleFunDiv
open Silmaril.Wasm.Interp.ExampleX
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.XRecursion Silmaril.Wasm.Abstract.XDiverge

theorem fdMod_valid : ((Validation.validate? fdMod).map fun mt => mt.imports.isEmpty) = some true :=
  by decide +kernel
theorem fdPrep_some : (prepare? evalConst? ({} : Store Empty) fdMod []).isSome = true :=
  by decide +kernel
theorem fdPrep_shape : fdPrep.1.code.isEmpty = true ∧ fdPrep.2.isNone = true := by decide +kernel
theorem fdStore_chkEB : storeChkEB tExt fdStore.funcs = true := by decide +kernel
theorem fdStore_wasmB : (fdStore.funcs.all fun fi => match fi.code with
    | .wasm _ => (Validation.DefType.funcType? fi.type).isSome
    | .host _ => false) = true := by decide +kernel

theorem fdPrep_eq : prepare? evalConst? ({} : Store Empty) fdMod [] = some fdPrep := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp fdPrep_some
  simp [fdPrep, hp]

/-- **`fdMod` instantiates to `fdPrep.1`**, at every profile and host. -/
theorem fd_instantiate (P : Numerics.Profile) (host : HostSemantics Empty) :
    Instantiate P host ({} : Store Empty) fdMod [] fdPrep.1 := by
  obtain ⟨mt, hmt, hnil⟩ : ∃ mt, Validation.validate? fdMod = some mt ∧ mt.imports.isEmpty := by
    rcases h : Validation.validate? fdMod with _ | mt
    · have hm := fdMod_valid
      simp [h] at hm
    · have hm := fdMod_valid
      simp only [h, Option.map_some, Option.some.injEq] at hm
      exact ⟨mt, rfl, hm⟩
  have himp : mt.imports = [] := List.isEmpty_iff.mp hnil
  have hvalid : ∃ xtE xtI, Validation.ModuleOk fdMod ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk ({} : Store Empty)) [] xtI :=
    ⟨mt.exports, mt.imports, by simpa using Validation.validate?_sound hmt, by rw [himp]; exact .nil⟩
  have hst : fdPrep.2 = none := Option.isNone_iff_eq_none.mp fdPrep_shape.2
  have h : Instantiate P host ({} : Store Empty) fdMod [] (fdPrep.1.withStart fdPrep.2) :=
    (prepare?_sound (P := P) (host := host) (c := fdPrep.1) (st := fdPrep.2) evalConst?_evalSound
      fdPrep_eq hvalid).2
  have hw : fdPrep.1.withStart fdPrep.2 = fdPrep.1 := by rw [hst]; rfl
  rwa [hw] at h

/-- **The store of the instance is typed.** -/
theorem fdStore_ok : StoreOk fdStore := by
  have hc : ConfigOk fdPrep.1 [] :=
    Instantiate.ok SingleThreaded.divHost_ok Binaryen.storeOk_empty
      (fd_instantiate (SingleThreaded.profile fun _ _ _ _ => false) SingleThreaded.divHost)
  exact SingleThreaded.ConfigOk.storeOk hc

/-- **The tail store check passes.** -/
theorem fdStore_chkE : StoreChkE tExt fdStore.funcs := by
  intro a fi fn ps rs hfi hcode hty
  have hb : funcChkEB tExt fdStore.funcs fi = true :=
    List.all_eq_true.mp fdStore_chkEB fi (List.mem_of_getElem? hfi)
  simpa only [funcChkEB, hcode, hty] using hb

/-- **The store's functions are Wasm functions with function types.** -/
theorem fdStore_wasmT : WasmFuncsT fdStore := by
  intro a fi hfi
  have hb := List.all_eq_true.mp fdStore_wasmB fi (List.mem_of_getElem? hfi)
  cases hc : fi.code with
  | wasm fn =>
    rw [hc] at hb
    obtain ⟨⟨ps, rs⟩, hty⟩ := Option.isSome_iff_exists.mp hb
    exact ⟨fn, ps, rs, rfl, hty⟩
  | host h => rw [hc] at hb; cases hb

/-- The instance of the functions. -/
abbrev fdMI : ModuleInst := (fdStore.funcs[0]?.map (·.module)).getD {}

theorem gi_spec (a : Nat) (g : Func) (h : a = 0 ∧ g = g0 ∨ a = 1 ∧ g = g1 ∨ a = 2 ∧ g = g2 ∨
    a = 3 ∧ g = g3 ∨ a = 4 ∧ g = g4) : ∃ fi : FuncInst Empty, fdStore.funcs[a]? = some fi ∧
    fi.code = .wasm g ∧ Validation.DefType.funcType? fi.type = some ([], []) ∧ fi.module = fdMI ∧
    fdMI.types[0]? = some fi.type := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem fd_invokeOk (a : Nat) (g : Func)
    (h : a = 0 ∧ g = g0 ∨ a = 1 ∧ g = g1 ∨ a = 2 ∧ g = g2 ∨ a = 3 ∧ g = g3 ∨ a = 4 ∧ g = g4) :
    InvokeOk fdStore a [] := by
  obtain ⟨fi, hfi, -, hty, -, -⟩ := gi_spec a g h
  exact ⟨fi, _, _, hfi, Proofs.Region.expand_of_funcType hty, by simp⟩

/-! ## Recursion through every call form: native extended divergence -/

abbrev F0 : Frame := Frame.forCall fdMI [] []

/-- **Function `0` diverges natively**: its `call_indirect` resolves (table `0`, slot `0`) to
itself. -/
theorem fd0_div : FunDivX fdStore 0 [] := by
  obtain ⟨fi, hfi, hc, hty, hm, hy⟩ := gi_spec 0 g0 (by simp)
  refine ⟨fi, g0, hfi, hc, ?_⟩
  rw [hm]
  refine evalDivX_of_coind (X := fun s f stk es => s = fdStore ∧ f = F0 ∧
    ((stk = [] ∧ es = Binaryen.liftInstrs g0.body) ∨
      (stk = [Val.i32 0] ∧ es = [.op (.callIndirect ⟨0⟩ ⟨0⟩) []]))) ?_ _ _ _ _
    ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩
  rintro s f stk es ⟨rfl, rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact .opK (fun x h => by cases h) .nil rfl ⟨rfl, rfl, .inr ⟨rfl, rfl⟩⟩
  · have hres : Silmaril.Wasm.Abstract.CallRes.IndRes fdStore F0 ⟨0⟩ ⟨0⟩ .i32 0 (some 0) := by
      refine .func (ta := 0) (ti := (fdStore.tables[0]?).getD ⟨⟨.i32, ⟨1, some 1⟩, .ref true .bot⟩, []⟩)
        rfl rfl ?_
      exact Silmaril.Wasm.Binaryen.DirectizeCast.refOk_cast hfi hy
        (PC.StoreOk.func_tyOk fdStore_ok hfi)
    exact .callIndCallee (stk₁ := []) .nil hres hfi hc hty
      ⟨rfl, by rw [hm]; rfl, .inl ⟨rfl, rfl⟩⟩

/-- **Function `1` diverges natively**: its `call_ref` (on global `0`) calls itself. -/
theorem fd1_div : FunDivX fdStore 1 [] := by
  obtain ⟨fi, hfi, hc, hty, hm, -⟩ := gi_spec 1 g1 (by simp)
  refine ⟨fi, g1, hfi, hc, ?_⟩
  rw [hm]
  refine evalDivX_of_coind (X := fun s f stk es => s = fdStore ∧ f = F0 ∧
    ((stk = [] ∧ es = Binaryen.liftInstrs g1.body) ∨
      (stk = [Val.ref (.func 1)] ∧ es = [.op (.callRef ⟨0⟩) []]))) ?_ _ _ _ _
    ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩
  rintro s f stk es ⟨rfl, rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact .opK (fun x h => by cases h) .nil rfl ⟨rfl, rfl, .inr ⟨rfl, rfl⟩⟩
  · exact .callRefCallee (stk₁ := []) .nil hfi hc hty ⟨rfl, by rw [hm]; rfl, .inl ⟨rfl, rfl⟩⟩

/-- **Function `2` diverges natively**: it tail-calls itself. -/
theorem fd2_div : FunDivX fdStore 2 [] := by
  obtain ⟨fi, hfi, hc, hty, hm, -⟩ := gi_spec 2 g2 (by simp)
  refine ⟨fi, g2, hfi, hc, ?_⟩
  rw [hm]
  refine evalDivX_of_coind (X := fun s f stk es => s = fdStore ∧ f = F0 ∧ stk = [] ∧
    es = Binaryen.liftInstrs g2.body) ?_ _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩
  rintro s f stk es ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨fi', hfun⟩ : ∃ fi', fdStore.func? F0 ⟨2⟩ = some (2, fi') := ⟨_, rfl⟩
  obtain rfl : fi' = fi := Option.some.inj ((funcs_of_func? hfun).symm.trans hfi)
  exact .tailCallee (stk₁ := []) .nil (.direct hfun) hfi hc hty ⟨rfl, by rw [hm]; rfl, rfl, rfl⟩

/-! ## Traps: a null table slot and a null reference -/

/-- **Function `3` traps**: its tail call goes through table `1`'s null slot. -/
theorem fd3_trap : ClosedOutcomeX fdStore 3 [] fdStore .trap := by
  obtain ⟨fi, hfi, hc, hty, hm, hy⟩ := gi_spec 3 g3 (by simp)
  refine ⟨fi, g3, [], [], Frame.forCall fi.module [] g3.locals, .trap, hfi, hc, hty, ?_, rfl⟩
  have hres : Silmaril.Wasm.Abstract.CallRes.IndRes fdStore (Frame.forCall fi.module [] g3.locals)
      ⟨1⟩ ⟨0⟩ .i32 0 none := by
    rw [hm]
    refine .null (ta := 1) (ti := (fdStore.tables[1]?).getD ⟨⟨.i32, ⟨1, some 1⟩, .ref true .bot⟩, []⟩)
      rfl rfl ?_
    show RefOk fdStore .null (fdMI.instRef ⟨true, .typeIdx ⟨0⟩⟩)
    rw [Silmaril.Wasm.Binaryen.DirectizeCast.instRef_typeIdx hy]
    exact .sub .null (.ref (.use (.dt (PC.StoreOk.func_tyOk fdStore_ok hfi)))) (.refNull .bot)
  exact .opOk (fun x h => by cases h) .nil rfl (.tailRes (args := []) .nil (.indirectTrap hres))

/-- **Function `4` traps**: its `call_ref` is on null (global `1`). -/
theorem fd4_trap : ClosedOutcomeX fdStore 4 [] fdStore .trap := by
  obtain ⟨fi, hfi, hc, hty, hm, -⟩ := gi_spec 4 g4 (by simp)
  refine ⟨fi, g4, [], [], Frame.forCall fi.module [] g4.locals, .trap, hfi, hc, hty, ?_, rfl⟩
  rw [hm]
  exact .opOk (fun x h => by cases h) .nil rfl (.callRefNull (stk₁ := []) .nil)

/-! ## Function level -/

/-- Each function of the store, through the two-way function theorem: `FunDivX` exactly when Core
diverges on its invocation exactly when the machine on its body is `MDivT`. -/
theorem fd_iff (o : SingleThreaded.GrowOracle) (a : Nat) (g : Func)
    (h : a = 0 ∧ g = g0 ∨ a = 1 ∧ g = g1 ∨ a = 2 ∧ g = g2 ∨ a = 3 ∧ g = g3 ∨ a = 4 ∧ g = g4) :
    ∃ fi : FuncInst Empty, fdStore.funcs[a]? = some fi ∧ fi.code = .wasm g ∧
      (FunDivX fdStore a [] ↔ Diverges (SingleThreaded.profile o) noHostX (invoke fdStore a [])) ∧
      (FunDivX fdStore a [] ↔
        Cfg.Machine.MDivT (SingleThreaded.profile o) noHostX (CX (closedCallX : Abstract.CallRel Empty))
          (Cfg.Function.calleeDivX o) g.body
          (Cfg.Machine.initial g.body fdStore (Frame.forCall fi.module [] g.locals))) := by
  obtain ⟨fi, hfi, hc, hty, -, -⟩ := gi_spec a g h
  have hok := fd_invokeOk a g h
  refine ⟨fi, hfi, hc, ?_, Cfg.Function.funDivX_iff_mdivT fdStore_ok hok fdStore_chkE fdStore_wasmT
    hfi hc hty⟩
  exact ((XProgress.invoke_closedX_adequacy (o := o) fdStore_ok hok fdStore_chkE fdStore_wasmT hfi
    hty).1).symm

end Silmaril.Wasm.Cfg.Proofs.ExampleFunDiv
