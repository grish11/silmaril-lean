module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.Root
public import Silmaril.Wasm.Component.DecoderBridge.FirstImp.Defs

/-!
# The definitions before the first core instantiation, with their trampolines

`FirstCore.Prefix.prefix_run` follows the definitions `preOk` allows before the first core
instantiation, keeping only the shapes of the frame and the core store. With the concrete engine
`core3 o` and root arguments that are all one component function `g0` (`importArgs hostI`), this
module keeps their contents:

* `lowFI h`, `lowStore n h`: the core store of `n` trampolines with host code `h`, of core type
  `fFlat`;
* `PreInvX g0 fx inst sc m ncf insts`: the component functions of the frame are all `g0`, of
  store entry `fx`; the core functions are the addresses `0, …, ncf - 1`; the core instances are
  the inline instances `insts` (each item a core function address); the core store is
  `lowStore ncf` of the trampoline `.lowered g0 fx.ft {} inst`;
* `prefix_runX`: the fold of `instantiateDef` over `pre` traps with a specification trap, or
  runs to a scope satisfying the invariant with `preLowers pre` more core functions and the
  inline instances `preInsts pre` appended.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.SingleThreaded (GrowOracle)
open Silmaril.Wasm.Execution.Core (Store FuncInst ExternAddr)

variable {o : GrowOracle} {σ : Type} {dispatch : Call (core3 o) → Canon.P (core3 o) σ (Ret (core3 o))}

/-! ## The store of trampolines -/

/-- A trampoline with host code `h`, of core type `fFlat`. -/
def lowFI {H : Type} (h : H) : FuncInst H :=
  ⟨Silmaril.Wasm.SingleThreaded.ofFlatType (Param.v1Type fFlat), {}, .host h⟩

/-- The core store of `n` trampolines with host code `h`. -/
def lowStore {H : Type} (n : Nat) (h : H) : Store H :=
  { ({} : Store H) with funcs := List.replicate n (lowFI h) }

theorem allocHost_lowStore {H : Type} (n : Nat) (h : H) :
    Silmaril.Wasm.SingleThreaded.allocHost (lowStore n h) (Param.v1Type fFlat) h =
      (lowStore (n + 1) h, n) := by
  simp only [Silmaril.Wasm.SingleThreaded.allocHost, Silmaril.Wasm.Execution.Core.allocFunc,
    lowStore, List.length_replicate, Prod.mk.injEq, and_true]
  rw [List.replicate_succ']
  rfl

theorem lowStore_zero {H : Type} (h : H) : lowStore 0 h = ({} : Store H) := rfl

/-! ## The invariant -/

/-- The core instances of the frame, as the inline instances `insts` read them. -/
def instsVal (insts : List (List (String × Nat))) : List (List (String × ExternAddr)) :=
  insts.map fun its => its.map fun p => (p.1, .func p.2)

/-- **What the frame and the core store hold before the first core instantiation.** -/
structure PreInvX (g0 : FuncId) (fx : CFuncInst (core3 o)) (inst : InstId) (sc : Scope (core3 o))
    (m : Machine.Config (core3 o) σ) (ncf : Nat) (insts : List (List (String × Nat))) : Prop where
  funcs : ∀ g ∈ sc.frame.funcs, g = g0
  fxGet : ArenaField.funcs.get? m.store g0 = some fx
  coreFuncs : sc.frame.coreFuncs = List.range ncf
  coreInsts : sc.frame.coreInstances = instsVal insts
  core : m.store.core = lowStore ncf (CanonHost.lowered g0 fx.ft {} inst)

/-- What a run of the definitions before the first core instantiation leaves. -/
def PreOutX (g0 : FuncId) (fx : CFuncInst (core3 o)) (inst : InstId)
    (m : Machine.Config (core3 o) σ) (mods : List (core3 o).Module) (ncf : Nat)
    (insts : List (List (String × Nat))) (sc' : Scope (core3 o))
    (m' : Machine.Config (core3 o) σ) : Prop :=
  ∃ c' nf' ncf', m' = { m with store := { m.store with core := c' } } ∧
    PreInv sc' m' nf' ncf' mods ∧ PreInvX g0 fx inst sc' m' ncf insts

/-- One definition. -/
def PreStepX (g0 : FuncId) (fx : CFuncInst (core3 o)) (inst : InstId)
    (m : Machine.Config (core3 o) σ) (nf ncf : Nat) (mods : List (core3 o).Module)
    (insts : List (List (String × Nat))) (sc' : Scope (core3 o))
    (m' : Machine.Config (core3 o) σ) : Prop :=
  ∃ c', m' = { m with store := { m.store with core := c' } } ∧ PreInv sc' m' nf ncf mods ∧
    PreInvX g0 fx inst sc' m' ncf insts

/-! ## One definition -/

section Defs

variable {R : Recurse (core3 o) σ} {inst : InstId} {outer : List (Frame (core3 o))}
  {args : Exports (core3 o)} {g0 : FuncId} {fx : CFuncInst (core3 o)}

theorem preStepX_refl {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {nf ncf : Nat}
    {mods : List (core3 o).Module} {insts : List (List (String × Nat))}
    (h : PreInv sc m nf ncf mods) (hx : PreInvX g0 fx inst sc m ncf insts) :
    PreStepX g0 fx inst m nf ncf mods insts sc m :=
  ⟨m.store.core, rfl, h, hx⟩

theorem stepX_coreModule {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {nf ncf : Nat}
    {mods : List (core3 o).Module} {insts : List (List (String × Nat))}
    (h : PreInv sc m nf ncf mods) (hx : PreInvX g0 fx inst sc m ncf insts)
    (mo : (core3 o).Module) :
    TOrT dispatch (instantiateDef R inst outer args sc (.coreModule mo)) m
      (PreStepX g0 fx inst m nf ncf (mods ++ [mo]) insts) := by
  rw [instDef_coreModuleG]
  exact TOrT.runs (TRuns.pure _ m) (preStepX_refl
    ⟨h.funcs_len, h.funcs_ok, h.coreFuncs_len, by simp [h.mods], h.lock⟩
    ⟨hx.funcs, hx.fxGet, hx.coreFuncs, hx.coreInsts, hx.core⟩)

theorem stepX_funcType {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {nf ncf : Nat}
    {mods : List (core3 o).Module} {insts : List (List (String × Nat))}
    (h : PreInv sc m nf ncf mods) (hx : PreInvX g0 fx inst sc m ncf insts)
    {ft : Syntax.FuncType} (hft : funcTypePrim ft = true) :
    TOrT dispatch (instantiateDef R inst outer args sc (.type (.func ft))) m
      (PreStepX g0 fx inst m nf ncf mods insts) := by
  obtain ⟨t, ht⟩ := resolveFuncType_prim sc.frame hft
  rw [instDef_funcTypeG sc ht]
  exact TOrT.runs (TRuns.pure _ m) (preStepX_refl
    ⟨h.funcs_len, h.funcs_ok, h.coreFuncs_len, h.mods, h.lock⟩
    ⟨hx.funcs, hx.fxGet, hx.coreFuncs, hx.coreInsts, hx.core⟩)

theorem stepX_import {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {nf ncf : Nat}
    {mods : List (core3 o).Module} {insts : List (List (String × Nat))}
    (h : PreInv sc m nf ncf mods) (hx : PreInvX g0 fx inst sc m ncf insts)
    (ha : ArgsOk args m) (hg0 : ∀ n v, args.lookup n = some v → v = .func g0)
    (n : Syntax.ExternName) (t : Nat) :
    TOrT dispatch (instantiateDef R inst outer args sc (.import_ n (.func t))) m
      (PreStepX g0 fx inst m (nf + 1) ncf mods insts) := by
  cases hl : args.lookup n.name with
  | none =>
    simp only [instantiateDef, hl, orTrap]
    exact TOrT.trap ((isSpecTrap_trap (r := .hostTrap _) (fun msg e => by cases e)).bind _)
  | some v =>
    obtain ⟨g, fi, rfl, hfi⟩ := ha _ _ hl
    have hg : g = g0 := by
      have := hg0 _ _ hl
      cases this
      rfl
    subst hg
    simp only [instantiateDef, hl, orTrap, pure_bind]
    refine TOrT.bind (Q := fun s m' => s = m.store ∧ m' = m) (TOrT.runs (TRuns.getStore m)
      ⟨rfl, rfl⟩) ?_
    intro s m' hq
    obtain ⟨hs, hm⟩ := hq
    rw [hs, hm]
    cases hc : importTypeCheck m.store sc.frame n.name (.func t) (.func g) with
    | error e =>
      simp only [checkImport]
      exact TOrT.trap ((isSpecTrap_trap (r := .hostTrap _) (fun msg e => by cases e)).bind _)
    | ok u =>
      simp only [checkImport, pure_bind, pushEntry, Syntax.ExternDesc.sort, Frame.push, need,
        orTrap]
      refine TOrT.runs (TRuns.pure _ m) (preStepX_refl ⟨?_, ?_, h.coreFuncs_len, h.mods, h.lock⟩
        ⟨?_, hx.fxGet, hx.coreFuncs, hx.coreInsts, hx.core⟩)
      · simp [h.funcs_len]
      · intro g' hg'
        rcases List.mem_append.mp hg' with hg' | hg'
        · exact h.funcs_ok g' hg'
        · rw [List.mem_singleton.mp hg']
          exact ⟨fi, hfi⟩
      · intro g' hg'
        rcases List.mem_append.mp hg' with hg' | hg'
        · exact hx.funcs g' hg'
        · exact List.mem_singleton.mp hg'

theorem stepX_lower {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {nf ncf : Nat}
    {mods : List (core3 o).Module} {insts : List (List (String × Nat))}
    (h : PreInv sc m nf ncf mods) (hx : PreInvX g0 fx inst sc m ncf insts)
    (hty : ∀ at_, (CanonHost.lowered g0 fx.ft {} inst : CanonHost (core3 o)).coreType at_ =
      Param.v1Type fFlat)
    {g : Nat} (hg : g < nf) :
    TOrT dispatch (instantiateDef R inst outer args sc (.canon (.lower g []))) m
      (PreStepX g0 fx inst m nf (ncf + 1) mods insts) := by
  have hg' : g < sc.frame.funcs.length := h.funcs_len ▸ hg
  have hgg : sc.frame.funcs[g] = g0 := hx.funcs _ (List.getElem_mem hg')
  have hr : resolveLower? sc.frame g [] = some (sc.frame.funcs[g], {}) := by
    simp only [resolveLower?, Frame.func?, List.getElem?_eq_getElem hg', resolveOpts?_nil]
    rfl
  simp only [instantiateDef, hr, need, orTrap, pure_bind, pushEntry, Frame.push]
  rw [hgg]
  have ha := TRuns.allocCoreHostG (σ := σ) (CanonHost.lowered g0 fx.ft {} inst) m
  refine TOrT.runs ((TRuns.getObjG ArenaField.funcs _ m hx.fxGet).bind (ha.bind (TRuns.pure _ _))) ?_
  rw [hty] at ha ⊢
  have hal : (core3 o).allocHost m.store.core (Param.v1Type fFlat)
      (CanonHost.lowered g0 fx.ft {} inst) =
      (lowStore (ncf + 1) (CanonHost.lowered g0 fx.ft {} inst), ncf) := by
    rw [hx.core]
    exact allocHost_lowStore _ _
  refine ⟨_, rfl, ⟨h.funcs_len, h.funcs_ok, ?_, h.mods, h.lock⟩, ⟨hx.funcs, hx.fxGet, ?_,
    hx.coreInsts, ?_⟩⟩
  · simp [h.coreFuncs_len]
  · show sc.frame.coreFuncs ++ [((core3 o).allocHost m.store.core (Param.v1Type fFlat)
      (CanonHost.lowered g0 fx.ft {} inst)).2] = List.range (ncf + 1)
    rw [hal, hx.coreFuncs, List.range_succ]
    rfl
  · show ((core3 o).allocHost m.store.core (Param.v1Type fFlat)
      (CanonHost.lowered g0 fx.ft {} inst)).1 = _
    rw [hal]

theorem items_mapM_val {f : Frame (core3 o)} {ncf : Nat} (hf : f.coreFuncs = List.range ncf) :
    ∀ items : List (String × Syntax.SortIdx Syntax.CoreSort),
      items.all (fun p => p.2.sort == .func && decide (p.2.idx < ncf)) = true →
      items.mapM (fun (p : String × Syntax.SortIdx Syntax.CoreSort) =>
        (p.1, ·) <$> externAt? f p.2) =
        some (items.map fun p => (p.1, ExternAddr.func p.2.idx))
  | [], _ => rfl
  | (n, ⟨srt, i⟩) :: items, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hi⟩, hr⟩ := h
    have hf' : @Eq (List Nat) f.coreFuncs (List.range ncf) := hf
    have hi' : i < f.coreFuncs.length := by
      have : f.coreFuncs.length = ncf :=
        (congrArg (@List.length Nat) hf').trans (List.length_range)
      omega
    rw [List.mapM_cons, items_mapM_val hf items (by simpa using hr)]
    have he : externAt? f ⟨.func, i⟩ = some (ExternAddr.func i) := by
      rw [externAt_func hi']
      congr 1
      show ExternAddr.func f.coreFuncs[i] = _
      congr 1
      have := congrArg (fun l => l[i]?) hf'
      simp only [List.getElem?_range hi] at this
      obtain ⟨_, h⟩ := List.getElem?_eq_some_iff.mp this
      exact h
    rw [he]
    rfl

theorem stepX_exports {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {nf ncf : Nat}
    {mods : List (core3 o).Module} {insts : List (List (String × Nat))}
    (h : PreInv sc m nf ncf mods) (hx : PreInvX g0 fx inst sc m ncf insts)
    {items : List (String × Syntax.SortIdx Syntax.CoreSort)}
    (hi : items.all (fun p => p.2.sort == .func && decide (p.2.idx < ncf)) = true) :
    TOrT dispatch (instantiateDef R inst outer args sc (.coreInstance (.exports items))) m
      (PreStepX g0 fx inst m nf ncf mods (insts ++ [items.map fun p => (p.1, p.2.idx)])) := by
  have hes := items_mapM_val hx.coreFuncs items hi
  simp only [instantiateDef, hes, need, orTrap, pure_bind, pushEntry, Frame.push]
  refine TOrT.runs (TRuns.pure _ m) (preStepX_refl
    ⟨h.funcs_len, h.funcs_ok, h.coreFuncs_len, h.mods, h.lock⟩
    ⟨hx.funcs, hx.fxGet, hx.coreFuncs, ?_, hx.core⟩)
  show sc.frame.coreInstances ++ [_] = _
  rw [hx.coreInsts]
  simp only [instsVal, List.map_append, List.map_cons, List.map_nil, List.map_map]
  rfl

end Defs

/-! ## The definitions before the first core instantiation -/

section Fold

variable {R : Recurse (core3 o) σ} {inst : InstId} {outer : List (Frame (core3 o))}
  {args : Exports (core3 o)} {g0 : FuncId} {fx : CFuncInst (core3 o)}

theorem preInvX_core {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {ncf : Nat}
    {insts : List (List (String × Nat))} (hx : PreInvX g0 fx inst sc m ncf insts)
    (c : Store (CanonHost (core3 o))) (hc : c = m.store.core) :
    PreInvX g0 fx inst sc { m with store := { m.store with core := c } } ncf insts :=
  ⟨hx.funcs, hx.fxGet, hx.coreFuncs, hx.coreInsts, by rw [hc]; exact hx.core⟩

/-- **The definitions before the first core instantiation, with their trampolines.** -/
theorem prefix_runX (hty : ∀ at_, (CanonHost.lowered g0 fx.ft {} inst : CanonHost (core3 o)).coreType
      at_ = Param.v1Type fFlat)
    (hg0 : ∀ n v, args.lookup n = some v → v = .func g0) :
    ∀ (pre : List (Syntax.Definition (core3 o).Module)) (nf ncf : Nat)
    (sc : Scope (core3 o)) (m : Machine.Config (core3 o) σ) (mods : List (core3 o).Module)
    (insts : List (List (String × Nat))), ArgsOk args m →
    preOk nf ncf pre = true → PreInv sc m nf ncf mods → PreInvX g0 fx inst sc m ncf insts →
    TOrT dispatch (pre.foldlM (instantiateDef R inst outer args) sc) m
      (PreOutX g0 fx inst m (mods ++ coreMods pre) (ncf + preLowers pre) (insts ++ preInsts pre))
  | [], nf, ncf, sc, m, mods, insts, _, _, h, hx =>
    TOrT.runs (TRuns.pure _ m) ⟨m.store.core, nf, ncf, rfl, by simpa [coreMods] using h,
      preInvX_core (by simpa [preLowers, preInsts] using hx) _ rfl⟩
  | d :: ds, nf, ncf, sc, m, mods, insts, ha, hp, h, hx => by
    rw [List.foldlM_cons]
    have cont : ∀ nf' ncf' mods' insts', preOk nf' ncf' ds = true →
        mods' ++ coreMods ds = mods ++ coreMods (d :: ds) →
        ncf' + preLowers ds = ncf + preLowers (d :: ds) →
        insts' ++ preInsts ds = insts ++ preInsts (d :: ds) →
        ∀ sc' m', PreStepX g0 fx inst m nf' ncf' mods' insts' sc' m' →
          TOrT dispatch (ds.foldlM (instantiateDef R inst outer args) sc') m'
            (PreOutX g0 fx inst m (mods ++ coreMods (d :: ds)) (ncf + preLowers (d :: ds))
              (insts ++ preInsts (d :: ds))) := by
      rintro nf' ncf' mods' insts' hp' hmods hncf hinsts sc' m' ⟨c', rfl, hinv, hinvx⟩
      refine (prefix_runX hty hg0 ds nf' ncf' sc' _ mods' insts' (argsOk_core ha c') hp' hinv
        hinvx).mono ?_
      rintro sc'' m'' ⟨c'', nf'', ncf'', rfl, hinv'', hinvx''⟩
      refine ⟨c'', nf'', ncf'', rfl, hmods ▸ hinv'', ?_⟩
      rw [← hncf, ← hinsts]
      exact ⟨hinvx''.funcs, hinvx''.fxGet, hinvx''.coreFuncs, hinvx''.coreInsts, hinvx''.core⟩
    match d, hp with
    | .coreModule mo, hp =>
      exact (stepX_coreModule h hx mo).bind (cont nf ncf _ insts hp (by simp [coreMods])
        (by simp [preLowers]) (by simp [preInsts]))
    | .type (.func ft), hp =>
      simp only [preOk, Bool.and_eq_true] at hp
      exact (stepX_funcType h hx hp.1).bind (cont nf ncf _ insts hp.2 (by simp [coreMods])
        (by simp [preLowers]) (by simp [preInsts]))
    | .import_ n (.func t), hp =>
      exact (stepX_import h hx ha hg0 n t).bind (cont (nf + 1) ncf _ insts hp
        (by simp [coreMods]) (by simp [preLowers]) (by simp [preInsts]))
    | .canon (.lower g []), hp =>
      simp only [preOk, Bool.and_eq_true, decide_eq_true_eq] at hp
      exact (stepX_lower h hx hty hp.1).bind (cont nf (ncf + 1) _ insts hp.2
        (by simp [coreMods]) (by simp [preLowers]; omega) (by simp [preInsts]))
    | .coreInstance (.exports items), hp =>
      simp only [preOk, Bool.and_eq_true] at hp
      exact (stepX_exports h hx hp.1).bind (cont nf ncf _ _ hp.2 (by simp [coreMods])
        (by simp [preLowers]) (by simp [preInsts]))

end Fold

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
