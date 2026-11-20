module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Root

/-!
# The first core instantiation against its trampolines

At the first core instantiation of a component of the fragment `FirstImpFrag`, the frame holds
the core functions `0, …, n - 1` (one trampoline each, `lowStore`) and the inline core
instances `preInsts pre`. The module's imports resolve, in order, to those trampolines:

* `externType_low`: a trampoline has the extern type `fExt` of a host function of core type
  `fFlat`;
* `coreImportsFor_low`: `coreImportsFor?` returns the function addresses `0, 1, …`, one per
  validated import type (`importsLowered`, `refTypesOk`);
* `instantiateCore_noneX`, `instantiateCore_startX`: the core instantiation traps `coreTrap` when
  preparation against them fails, and reaches the start function when it reports one (as
  `FirstCore.Root.instantiateCore_none`, `instantiateCore_start` for a module with imports).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.SingleThreaded (GrowOracle)
open Silmaril.Wasm.Execution.Core (Store ExternAddr)

/-! ## Import resolution -/

section Resolve

variable {H : Type}

theorem externType_low (n : Nat) (h : H) {i : Nat} (hi : i < n) :
    Core3.externTypeE? (lowStore n h) (.func i) = fExt := by
  have h₁ : Silmaril.Wasm.Execution.Core.externAddrType? (lowStore n h) (.func i) =
      Silmaril.Wasm.Execution.Core.externAddrType? fStore (.func 0) := by
    simp only [Silmaril.Wasm.Execution.Core.externAddrType?, lowStore,
      List.getElem?_replicate, hi, ↓reduceIte]
    rfl
  unfold fExt Core3.externTypeE?
  rw [h₁]

theorem lookup_map_func (its : List (String × Nat)) (nm : String) :
    (its.map fun p => (p.1, ExternAddr.func p.2)).lookup nm = (its.lookup nm).map ExternAddr.func := by
  induction its with
  | nil => rfl
  | cons p its ih =>
    rcases p with ⟨k, v⟩
    simp only [List.map_cons, List.lookup]
    cases nm == k <;> simp [ih]

variable {o : GrowOracle}

/-- One import of the fragment resolves to its trampoline. -/
theorem coreImportFor_low {f : Frame (core3 o)} {insts : List (List (String × Nat))} {n : Nat}
    {h : CanonHost (core3 o)} {cargs : List (String × Nat)} (hfi : f.coreInstances = instsVal insts)
    {τ : Core3.ExtT} (hτ : fExt = some τ) {mn nm : String} {τ' : Core3.ExtT} {i : Nat}
    (hi : i < n) (hidx : importIdx cargs insts mn nm = some i)
    (hsub : Silmaril.Wasm.Validation.ExternSub {} τ.1 τ'.1) :
    coreImportFor? (E := core3 o) (lowStore n h) cargs f (mn, nm, τ') = some (.func i) := by
  simp only [importIdx, bind, Option.bind_eq_some_iff] at hidx
  obtain ⟨j, hj, its, hits, hl⟩ := hidx
  have hci : f.coreInstance? j = some (its.map fun p => (p.1, ExternAddr.func p.2)) := by
    have h0 : (instsVal insts)[j]? = some (its.map fun p => (p.1, ExternAddr.func p.2)) := by
      simp only [instsVal, List.getElem?_map, hits, Option.map_some]
    simp only [Frame.coreInstance?, hfi]
    exact h0
  have hlk : lookupExport? (its.map fun p => (p.1, ExternAddr.func p.2)) nm =
      some (ExternAddr.func i) := by
    simp only [lookupExport?, lookup_map_func, hl, Option.map_some]
  have hext : (core3 o).externType? (lowStore n h) (ExternAddr.func i) = some τ :=
    (externType_low n h hi).trans hτ
  simp only [coreImportFor?, hj, Option.bind_eq_bind, Option.bind_some]
  erw [hci, Option.bind_some, hlk, Option.bind_some, hext, Option.bind_some]
  exact ite_eq_left_of_eq_true _ _ (eq_true hsub)

theorem importsLowered_get {cargs : List (String × Nat)} {insts : List (List (String × Nat))}
    {md : Silmaril.Wasm.Module} (h : importsLowered cargs insts md = true) {i : Nat}
    (hi : i < md.imports.length) :
    importIdx cargs insts md.imports[i].moduleName md.imports[i].name = some i := by
  unfold importsLowered at h
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  rw [List.getElem?_eq_getElem hi] at this
  simpa using this

theorem mapM_range_func {α : Type} (F : α → Option ExternAddr) (l : List α)
    (hF : ∀ i (hi : i < l.length), F l[i] = some (.func i)) :
    l.mapM F = some ((List.range l.length).map ExternAddr.func) := by
  refine List.mapM_eq_some_iff_forall₂.mpr
    (List.forall₂_of_length_eq_of_get (by simp) fun i h₁ h₂ => ?_)
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
  exact hF i h₁

/-- **The imports of the first instantiated module resolve to the trampolines.** -/
theorem coreImportsFor_low {f : Frame (core3 o)} {insts : List (List (String × Nat))}
    {h : CanonHost (core3 o)} {cargs : List (String × Nat)} {md : Silmaril.Wasm.Module}
    (hfi : f.coreInstances = instsVal insts) (hlow : importsLowered cargs insts md = true)
    (hrt : refTypesOk md = true) :
    coreImportsFor? (E := core3 o) (lowStore md.imports.length h) md cargs f =
      some ((List.range (Core3.importTypesE md).length).map ExternAddr.func) := by
  unfold coreImportsFor?
  show (Core3.importTypesE md).mapM _ = _
  unfold refTypesOk at hrt
  cases hτ : fExt with
  | none => rw [hτ] at hrt; cases hrt
  | some τ =>
    rw [hτ] at hrt
    cases hv : Silmaril.Wasm.Validation.validate? md with
    | none =>
      rw [Core3.importTypesE_of_none hv]
      rfl
    | some mt =>
      have he := Core3.importTypesE_eq hv
      have hlen : (Core3.importTypesE md).length ≤ md.imports.length := by
        have := congrArg List.length he
        simp only [List.length_map, List.length_zip] at this
        omega
      refine mapM_range_func _ _ fun i h₁ => ?_
      have hi : i < md.imports.length := by omega
      have hz : i < (List.map (fun p => (p.1, p.2.1, p.2.2.1)) (Core3.importTypesE md)).length := by
        simpa using h₁
      have he' := List.getElem_of_eq he hz
      simp only [List.getElem_map, List.getElem_zip, Prod.mk.injEq] at he'
      have hsub := List.all_eq_true.mp hrt _ (List.getElem_mem h₁)
      simp only [decide_eq_true_eq] at hsub
      have key := coreImportFor_low (h := h) (cargs := cargs) hfi hτ (τ' := (Core3.importTypesE md)[i].2.2)
        hi (importsLowered_get hlow hi) hsub
      rw [← he'.1, ← he'.2.1] at key
      exact key

end Resolve

/-! ## The core instantiation -/

section Core

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)} [∀ a b, Decidable (E.ExternSub a b)]

/-- **Preparation against the trampolines fails**: the core instantiation traps `coreTrap`. -/
theorem instantiateCore_noneX {f : Frame E} {mi : Nat} {cargs : List (String × Nat)}
    {md : E.Module} {m₁ : Machine.Config E σ} {xs : List E.ExternVal}
    (hmd : f.coreModule? mi = some md) (hc : coreImportsFor? m₁.store.core md cargs f = some xs)
    (hp : E.prepare? m₁.store.core md xs = none) :
    ∃ tr mT, TrapsQS dispatch none (instantiateCore ⟨0⟩ f mi cargs) m₁ tr mT := by
  unfold instantiateCore
  simp only [hmd, need, orTrap, pure_bind]
  obtain ⟨tr, hrun, -⟩ := SRuns.runsQ (dispatch := dispatch) (TRuns.getStore m₁) none
  refine ⟨tr ++ [], m₁, .bind hrun ?_⟩
  simp only [hc, pure_bind, hp]
  exact .trap _ (isSpecTrap_trap (fun _ h => by cases h))

/-- **Preparation against the trampolines reports a start function**: the core instantiation
reaches it, the core store replaced. -/
theorem instantiateCore_startX {f : Frame E} {mi : Nat} {cargs : List (String × Nat)}
    {md : E.Module} {m₁ : Machine.Config E σ} {xs : List E.ExternVal}
    {core' : E.Store (CanonHost E)} {ci : E.Inst} {sf : E.FuncAddr}
    (hmd : f.coreModule? mi = some md) (hc : coreImportsFor? m₁.store.core md cargs f = some xs)
    (hp : E.prepare? m₁.store.core md xs = some (core', ci, some sf)) :
    FocusAt prof hr dispatch none (Instantiate.runStart ⟨0⟩ sf) (instantiateCore ⟨0⟩ f mi cargs) m₁
      { m₁ with store := setCoreSt core' m₁.store } := by
  unfold instantiateCore
  simp only [hmd, need, orTrap, pure_bind]
  refine FocusAt.silent (TRuns.getStore m₁) ?_
  simp only [hc, pure_bind, hp]
  refine FocusAt.silent (TRuns.modifyStore (f := setCoreSt core') (fun _ => rfl) m₁) ?_
  exact FocusAt.here _ _

end Core

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
