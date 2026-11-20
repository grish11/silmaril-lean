module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.GapRun
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Sim
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Core
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Start

/-!
# A later core instantiation in the shared core store: preparation

The IR prepares a later node's module `m` alone, against its imports `irStore b` (`b` host
functions of core type `fFlat`); the reference machine prepares it in the shared core store `σ`,
whose first `b` functions are trampolines of `f` (`lowFI lowH`), against the first `b` functions.
With the gap `⟨σ, b⟩` (`Multi.GapShift`):

* `rel_irStore`, `preOk_irStore`: `σ` is the gap image of `irStore b` (host code renamed by `gL`),
  whose functions are related;
* `externAddrType_gap`, `externAddrsOk_gap`: import checks are the same;
* **`prepareE_gap`**: the reference preparation is the IR's, its store renamed and mapped into the
  shared store, its module instance and start function mapped;
* `coreImportsFor_shared`: the imports of `m`, wired in order to the trampolines through the inline
  core instances of the frame, resolve to the first `b` functions of `σ`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.SingleThreaded (GrowOracle neverFail)

variable {H : Type}

/-! ## The IR's import store in the shared store -/

theorem store_app_empty (s : Store H) : Store.app s {} = s := by
  obtain ⟨⟩ := s
  simp [Store.app]

/-- The trampolines of the shared store, as the gap image of the IR's import store. -/
theorem rel_irStore (g : Gap (CanonHost (core3 neverFail))) :
    g.rel (Store.mapH FirstImp.gL (irStore g.b)) = g.pre := by
  have h : ({ Store.mapH FirstImp.gL (irStore g.b) with
      funcs := (Store.mapH FirstImp.gL (irStore g.b)).funcs.drop g.b } : Store _) = {} := by
    simp [Store.mapH, irStore]
  rw [Gap.rel, h]
  have h₂ : g.sh.store ({} : Store (CanonHost (core3 neverFail))) = {} := rfl
  rw [h₂, store_app_empty]

theorem mapH_irStore_funcs (n : Nat) :
    (Store.mapH FirstImp.gL (irStore n)).funcs = List.replicate n (lowFI lowH) := by
  rw [mapH_irStore]
  rfl

theorem finst_lowFI (δ : GShift) : δ.finst (lowFI (lowH : CanonHost (core3 neverFail))) =
    lowFI lowH := rfl

/-- **The trampolines relate the IR's import store to the shared store.** -/
theorem preOk_irStore (g : Gap (CanonHost (core3 neverFail)))
    (h : ∀ i, i < g.b → g.pre.funcs[i]? = some (lowFI lowH)) :
    g.PreOk (Store.mapH FirstImp.gL (irStore g.b)).funcs := by
  refine ⟨by rw [mapH_irStore_funcs, List.length_replicate], fun a ha => ?_⟩
  rw [h a ha, mapH_irStore_funcs, List.getElem?_replicate]
  simp only [ha, ↓reduceIte, Option.map_some, finst_lowFI]

/-! ## Import checks -/

section Checks

variable (g : Gap H)

theorem externAddrType_gap {u : Store H} (hP : g.PreOk u.funcs) (xa : ExternAddr) :
    externAddrType? (g.rel u) (g.sh.xa xa) = externAddrType? u xa := by
  cases xa with
  | func a =>
    simp only [GShift.xa, externAddrType?, funcs_gap g hP a, Option.map_map]
    rfl
  | tag a =>
    simp only [GShift.xa, externAddrType?, Gap.rel, Store.app, GShift.store, sh_tg]
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  | global a =>
    simp only [GShift.xa, externAddrType?, rel_globals, sh_gl]
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_map, Option.map_map]
    rfl
  | mem a =>
    simp only [GShift.xa, externAddrType?, Gap.rel, Store.app, GShift.store, sh_me]
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  | table a =>
    simp only [GShift.xa, externAddrType?, Gap.rel, Store.app, GShift.store, sh_ta]
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_map, Option.map_map]
    rfl

theorem externAddrsOk_gap {u : Store H} (hP : g.PreOk u.funcs) :
    ∀ (xas : List ExternAddr) (ts : List CExternType),
      externAddrsOk? (g.rel u) (xas.map g.sh.xa) ts = externAddrsOk? u xas ts
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | xa :: xas, t :: ts => by
    simp only [List.map_cons, externAddrsOk?, externAddrOk?, externAddrType_gap g hP,
      externAddrsOk_gap hP xas ts]

end Checks

/-! ## Preparation -/

theorem range_xa (g : Gap H) (n : Nat) (hn : n ≤ g.b) :
    ((List.range n).map ExternAddr.func).map g.sh.xa = (List.range n).map ExternAddr.func := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply, GShift.xa, sh_fn]
  rw [fnMap_lt g (Nat.lt_of_lt_of_le (List.mem_range.mp hi) hn)]

/-- **Preparation in the shared store is the IR's, mapped**, for a module without data and element
segments whose `b` imports are the first `b` functions (the trampolines) of the shared store. -/
theorem prepareE_gap (g : Gap (CanonHost (core3 neverFail)))
    (htr : ∀ i, i < g.b → g.pre.funcs[i]? = some (lowFI lowH)) {m : Module}
    (hseg : m.data = [] ∧ m.elems = []) :
    Core3.prepareE? g.pre m ((List.range g.b).map ExternAddr.func) =
      (Core3.prepareE? (irStore g.b) m ((List.range g.b).map ExternAddr.func)).map
        (fun p => (g.rel (Store.mapH FirstImp.gL p.1), g.sh.minst p.2.1, p.2.2.map g.sh.fn)) := by
  have hP := preOk_irStore g htr
  have hb : g.b ≤ (Store.mapH FirstImp.gL (irStore g.b)).funcs.length := hP.1
  have e₁ := prepareE_mapH FirstImp.gL (irStore g.b) m ((List.range g.b).map ExternAddr.func)
  rw [show (fun (p : Store Nat × ModuleInst × Option Nat) =>
      (g.rel (Store.mapH FirstImp.gL p.1), g.sh.minst p.2.1, p.2.2.map g.sh.fn)) =
      (fun (p : Store (CanonHost (core3 neverFail)) × ModuleInst × Option Nat) =>
        (g.rel p.1, g.sh.minst p.2.1, p.2.2.map g.sh.fn)) ∘
      (fun (p : Store Nat × ModuleInst × Option Nat) => (Store.mapH FirstImp.gL p.1, p.2.1, p.2.2))
      from rfl, ← Option.map_map, ← e₁]
  conv => lhs; rw [← rel_irStore g, ← range_xa g g.b (Nat.le_refl _)]
  unfold Core3.prepareE?
  cases validate? m with
  | none => rfl
  | some mt =>
    dsimp only
    rw [externAddrsOk_gap g hP]
    split_ifs
    · rw [instantiateOnce?_gap g _ hb m _ hseg]
      cases instantiateOnce? (Store.mapH FirstImp.gL (irStore g.b)) m _ with
      | none => rfl
      | some p =>
        obtain ⟨s', f', st⟩ := p
        cases st with
        | none => rfl
        | some x =>
          simp only [Option.map_some]
          show ((g.sh.minst f'.module).funcs[x.toNat]?).map _ = _
          simp only [GShift.minst, List.getElem?_map]
          cases f'.module.funcs[x.toNat]? <;> rfl
    · rfl

/-! ## Import resolution -/

section Resolve

variable {o : GrowOracle}

theorem externType_tramp {s : Store (CanonHost (core3 o))} {h : CanonHost (core3 o)} {n i : Nat}
    (hi : i < n) (htr : s.funcs[i]? = some (lowFI h)) :
    Core3.externTypeE? s (.func i) = fExt := by
  rw [← externType_low n h hi]
  unfold Core3.externTypeE?
  simp only [externAddrType?, htr, lowStore, List.getElem?_replicate, hi, ↓reduceIte]

/-- One import, wired through an inline core instance to the trampoline `i`, resolves to it. -/
theorem coreImportFor_shared {f : Frame (core3 o)} {insts : List (List (String × Nat))}
    {s : Store (CanonHost (core3 o))} {h : CanonHost (core3 o)} {cargs : List (String × Nat)}
    (hfi : ∃ X : List (List (String × ExternAddr)),
      f.coreInstances = (instsVal insts ++ X : List (List (String × ExternAddr))))
    {τ : Core3.ExtT} (hτ : fExt = some τ) {mn nm : String} {τ' : Core3.ExtT} {i : Nat}
    (htr : s.funcs[i]? = some (lowFI h)) (hidx : importIdx cargs insts mn nm = some i)
    (hsub : ExternSub {} τ.1 τ'.1) :
    coreImportFor? (E := core3 o) s cargs f (mn, nm, τ') = some (.func i) := by
  obtain ⟨X, hX⟩ := hfi
  simp only [importIdx, bind, Option.bind_eq_some_iff] at hidx
  obtain ⟨j, hj, its, hits, hl⟩ := hidx
  have hjl : j < insts.length := (List.getElem?_eq_some_iff.mp hits).1
  have hci : f.coreInstance? j = some (its.map fun p => (p.1, ExternAddr.func p.2)) := by
    have h0 : (instsVal insts ++ X)[j]? = some (its.map fun p => (p.1, ExternAddr.func p.2)) := by
      rw [List.getElem?_append_left (by simpa [instsVal] using hjl)]
      simp only [instsVal, List.getElem?_map, hits, Option.map_some]
    simp only [Frame.coreInstance?, hX]
    exact h0
  have hlk : lookupExport? (its.map fun p => (p.1, ExternAddr.func p.2)) nm =
      some (ExternAddr.func i) := by
    simp only [lookupExport?, lookup_map_func, hl, Option.map_some]
  have hext : (core3 o).externType? s (ExternAddr.func i) = some τ :=
    (externType_tramp (Nat.lt_succ_self i) htr).trans hτ
  simp only [coreImportFor?, hj, Option.bind_eq_bind, Option.bind_some]
  erw [hci, Option.bind_some, hlk, Option.bind_some, hext, Option.bind_some]
  exact ite_eq_left_of_eq_true _ _ (eq_true hsub)

/-- **The imports of a later module resolve to the trampolines of the shared store.** -/
theorem coreImportsFor_shared {f : Frame (core3 o)} {insts : List (List (String × Nat))}
    {s : Store (CanonHost (core3 o))} {h : CanonHost (core3 o)} {cargs : List (String × Nat)}
    {md : Module}
    (hfi : ∃ X : List (List (String × ExternAddr)),
      f.coreInstances = (instsVal insts ++ X : List (List (String × ExternAddr))))
    (htr : ∀ i, i < md.imports.length → s.funcs[i]? = some (lowFI h))
    (hlow : importsLowered cargs insts md = true) (hrt : refTypesOk md = true) :
    coreImportsFor? (E := core3 o) s md cargs f =
      some ((List.range (Core3.importTypesE md).length).map ExternAddr.func) := by
  unfold coreImportsFor?
  show (Core3.importTypesE md).mapM _ = _
  unfold refTypesOk at hrt
  cases hτ : fExt with
  | none => rw [hτ] at hrt; cases hrt
  | some τ =>
    rw [hτ] at hrt
    cases hv : validate? md with
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
      have key := coreImportFor_shared (s := s) (h := h) (cargs := cargs) hfi hτ
        (τ' := (Core3.importTypesE md)[i].2.2) (htr i hi) (importsLowered_get hlow hi) hsub
      rw [← he'.1, ← he'.2.1] at key
      exact key

end Resolve

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
