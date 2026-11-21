module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.Path
public import Silmaril.Proofs.Wasm.Component.Reference.InstNest
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.TrapS
public import Silmaril.Wasm.Component.DecoderBridge.FirstCore.Defs

/-!
# The definitions before the first core instantiation, over any engine

The definitions `preOk` allows before the first core instantiation run silently or trap with a
specification trap (a missing or ill-typed import):

* `TOrT p m Q`: the program `p` traps from `m` with a specification trap (`TrapsQS`), or runs
  silently (`TRuns`) to a result and configuration satisfying `Q`; `TOrT.bind` sequences;
* `PreInv args sc m nf ncf mods`: the frame of `sc` has `nf` component functions, all allocated in
  `m`'s store, `ncf` core functions and the core modules `mods`; the store is unlocked;
* `HostAllocs c c'`: `c'` is `c` after host allocations (`E.allocHost`);
* `prefix_run`: from such a scope, the fold of `instantiateDef` over definitions `pre` with
  `preOk nf ncf pre` traps, or runs to a scope with the core modules `mods ++ coreMods pre`,
  changing only the core store, by host allocations.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate

variable {E : CoreEngine} {σ : Type} {dispatch : Call E → Canon.P E σ (Ret E)}

/-! ## Silent runs or specification traps -/

variable (dispatch) in
/-- The program `p` traps from `m` with a specification trap, or runs silently to a result and
a configuration satisfying `Q`. -/
def TOrT {α : Type} (p : Canon.P E σ α) (m : Machine.Config E σ)
    (Q : α → Machine.Config E σ → Prop) : Prop :=
  (∃ tr mT, TrapsQS dispatch none p m tr mT) ∨ ∃ a m', TRuns p m a m' ∧ Q a m'

namespace TOrT

theorem bind {α β : Type} {p : Canon.P E σ α} {f : α → Canon.P E σ β} {m : Machine.Config E σ}
    {Q : α → Machine.Config E σ → Prop} {Q' : β → Machine.Config E σ → Prop}
    (h : TOrT dispatch p m Q) (h' : ∀ a m', Q a m' → TOrT dispatch (f a) m' Q') :
    TOrT dispatch (p >>= f) m Q' := by
  rcases h with ⟨tr, mT, ht⟩ | ⟨a, m₁, hr, hq⟩
  · exact .inl ⟨tr, mT, .left ht⟩
  · rcases h' a m₁ hq with ⟨tr, mT, ht⟩ | ⟨b, m₂, hr₂, hq₂⟩
    · obtain ⟨tr₁, hr₁, -⟩ := SRuns.runsQ (dispatch := dispatch) hr none
      exact .inl ⟨_, _, .bind hr₁ ht⟩
    · exact .inr ⟨b, m₂, hr.bind hr₂, hq₂⟩

theorem runs {α : Type} {p : Canon.P E σ α} {m m' : Machine.Config E σ} {a : α}
    {Q : α → Machine.Config E σ → Prop} (h : TRuns p m a m') (hq : Q a m') :
    TOrT dispatch p m Q :=
  .inr ⟨a, m', h, hq⟩

theorem trap {α : Type} {p : Canon.P E σ α} {m : Machine.Config E σ}
    {Q : α → Machine.Config E σ → Prop} (h : Adequacy.IsSpecTrap p) : TOrT dispatch p m Q :=
  .inl ⟨[], m, .trap m h⟩

theorem mono {α : Type} {p : Canon.P E σ α} {m : Machine.Config E σ}
    {Q Q' : α → Machine.Config E σ → Prop} (h : TOrT dispatch p m Q)
    (hQ : ∀ a m', Q a m' → Q' a m') : TOrT dispatch p m Q' := by
  rcases h with h | ⟨a, m', hr, hq⟩
  · exact .inl h
  · exact .inr ⟨a, m', hr, hQ a m' hq⟩

end TOrT

theorem isSpecTrap_trap {α : Type} {r : TrapReason} (hr : ∀ msg, r ≠ .internal msg) :
    Adequacy.IsSpecTrap (trap r : Canon.P E σ α) :=
  ⟨r, _, hr, rfl⟩

/-! ## Host allocations -/

/-- `c'` is the core store `c` after host allocations. -/
inductive HostAllocs (E : CoreEngine) : E.Store (CanonHost E) → E.Store (CanonHost E) → Prop
  | refl (c : E.Store (CanonHost E)) : HostAllocs E c c
  | step {c c' : E.Store (CanonHost E)} (ty : Silmaril.Wasm.V1.FuncType) (h : CanonHost E) :
      HostAllocs E c c' → HostAllocs E c (E.allocHost c' ty h).1

theorem HostAllocs.trans {c₁ c₂ c₃ : E.Store (CanonHost E)} (h₁ : HostAllocs E c₁ c₂)
    (h₂ : HostAllocs E c₂ c₃) : HostAllocs E c₁ c₃ := by
  induction h₂ with
  | refl => exact h₁
  | step ty h _ ih => exact .step ty h ih

/-! ## The invariant -/

/-- The root arguments are allocated component functions of `m`'s store. -/
def ArgsOk (args : Exports E) (m : Machine.Config E σ) : Prop :=
  ∀ n v, args.lookup n = some v → ∃ g fi, v = .func g ∧ ArenaField.funcs.get? m.store g = some fi

/-- What the frame holds before the first core instantiation. -/
structure PreInv (sc : Scope E) (m : Machine.Config E σ) (nf ncf : Nat) (mods : List E.Module) :
    Prop where
  funcs_len : sc.frame.funcs.length = nf
  funcs_ok : ∀ g ∈ sc.frame.funcs, ∃ fi, ArenaField.funcs.get? m.store g = some fi
  coreFuncs_len : sc.frame.coreFuncs.length = ncf
  mods : sc.frame.coreModules = mods
  lock : m.store.lockdown = false

/-- What a run of the definitions before the first core instantiation leaves: only the core
store changed, by host allocations, and the frame satisfies the invariant. -/
def PreOut (m : Machine.Config E σ) (mods : List E.Module) (sc' : Scope E)
    (m' : Machine.Config E σ) : Prop :=
  ∃ c' nf' ncf', m' = { m with store := { m.store with core := c' } } ∧
    HostAllocs E m.store.core c' ∧ PreInv sc' m' nf' ncf' mods

/-! ## One definition -/

section Defs

theorem instDef_coreModuleG [∀ a b, Decidable (E.ExternSub a b)] {R : Recurse E σ} {inst : InstId}
    {outer : List (Frame E)} {args : Exports E} (sc : Scope E) (mo : E.Module) :
    instantiateDef R inst outer args sc (.coreModule mo) =
      (Pure.pure { sc with frame := { sc.frame with coreModules := sc.frame.coreModules ++ [mo] } } :
        Canon.P E σ (Scope E)) := by
  simp only [instantiateDef, pushEntry, need, Frame.push, orTrap]
  rfl

theorem resolveParams_prim (f : Frame E) :
    ∀ ps : List (String × Syntax.VT), ps.all (fun p => vtPrim p.2) = true →
      ∃ l, ps.mapM (fun (p : String × Syntax.VT) => (p.1, ·) <$> resolveValType? f p.2) = some l
  | [], _ => ⟨[], rfl⟩
  | (n, .prim q) :: ps, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨l, hl⟩ := resolveParams_prim f ps h.2
    refine ⟨(n, primType q) :: l, ?_⟩
    rw [List.mapM_cons, hl]
    rfl
  | (_, .idx _) :: _, h => by simp [vtPrim] at h

theorem resolveFuncType_prim (f : Frame E) {ft : Syntax.FuncType} (h : funcTypePrim ft = true) :
    ∃ t, resolveFuncType? f ft = some t := by
  simp only [funcTypePrim, Bool.and_eq_true] at h
  obtain ⟨l, hl⟩ := resolveParams_prim f ft.params h.1
  have hr : ∃ r, resolveOptValType? f ft.result = some r := by
    rcases hres : ft.result with _ | (q | i)
    · exact ⟨none, rfl⟩
    · exact ⟨some (primType q), rfl⟩
    · rw [hres] at h; simp [vtPrim] at h
  obtain ⟨r, hr⟩ := hr
  refine ⟨{ params := l, result := r, async_ := ft.async_ }, ?_⟩
  simp only [resolveFuncType?]
  rw [hl, hr]
  rfl

theorem instDef_funcTypeG [∀ a b, Decidable (E.ExternSub a b)] {R : Recurse E σ} {inst : InstId}
    {outer : List (Frame E)} {args : Exports E} (sc : Scope E) {ft : Syntax.FuncType} {t : Types.FuncType RtId}
    (h : resolveFuncType? sc.frame ft = some t) :
    instantiateDef R inst outer args sc (.type (.func ft)) =
      (Pure.pure { sc with frame := { sc.frame with types := sc.frame.types ++ [.func t] } } :
        Canon.P E σ (Scope E)) := by
  simp only [instantiateDef, staticType?, h, Option.map_some, need, orTrap, pushEntry,
    Frame.push, pure_bind]

theorem TRuns.getObjG {Id α : Type} (F : ArenaField E Id α) (i : Id) {x : α}
    (m : Machine.Config E σ) (h : F.get? m.store i = some x) :
    TRuns (Canon.getObj F i : Canon.P E σ α) m x m := by
  refine .get ?_
  show TRuns (match F.get? m.store i with
    | some x => Pure.pure x | none => internal "dangling arena id") m x m
  rw [h]
  exact TRuns.pure x m

theorem TRuns.allocCoreHostG (h : CanonHost E) (m : Machine.Config E σ) :
    TRuns (Instantiate.allocCoreHost h : Canon.P E σ _) m
      (E.allocHost m.store.core (h.coreType (addrTypesOf m.store)) h).2
      { m with store := allocHostSt (h.coreType (addrTypesOf m.store)) h m.store } :=
  (TRuns.getStore m).bind ((TRuns.modifyStore
    (f := allocHostSt (h.coreType (addrTypesOf m.store)) h) (fun _ => rfl) m).bind
    (TRuns.pure _ _))

theorem externAt_func {f : Frame E} {i : Nat} (h : i < f.coreFuncs.length) :
    externAt? f ⟨.func, i⟩ = some (E.ofFunc f.coreFuncs[i]) := by
  simp [externAt?, Frame.get?, Frame.coreFunc?, List.getElem?_eq_getElem h, Entry.toExtern?]

theorem items_mapM {f : Frame E} :
    ∀ items : List (String × Syntax.SortIdx Syntax.CoreSort),
      items.all (fun p => p.2.sort == .func && decide (p.2.idx < f.coreFuncs.length)) = true →
      ∃ es, items.mapM (fun (p : String × Syntax.SortIdx Syntax.CoreSort) =>
        (p.1, ·) <$> externAt? f p.2) = some es
  | [], _ => ⟨[], rfl⟩
  | (n, ⟨srt, i⟩) :: items, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hi⟩, hr⟩ := h
    obtain ⟨es, hes⟩ := items_mapM items (by simpa using hr)
    refine ⟨(n, E.ofFunc f.coreFuncs[i]) :: es, ?_⟩
    rw [List.mapM_cons, hes]
    simp [externAt_func hi]

end Defs

/-! ## The definitions before the first core instantiation -/

section Fold

variable [∀ a b, Decidable (E.ExternSub a b)] {R : Recurse E σ} {inst : InstId}
  {outer : List (Frame E)} {args : Exports E}

/-- One definition: only the core store changed, by host allocations, and the frame satisfies
the invariant with `nf` component and `ncf` core functions and the core modules `mods`. -/
def PreStep (m : Machine.Config E σ) (nf ncf : Nat) (mods : List E.Module) (sc' : Scope E)
    (m' : Machine.Config E σ) : Prop :=
  ∃ c', m' = { m with store := { m.store with core := c' } } ∧ HostAllocs E m.store.core c' ∧
    PreInv sc' m' nf ncf mods

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem preStep_refl {sc : Scope E} {m : Machine.Config E σ} {nf ncf : Nat}
    {mods : List E.Module} (h : PreInv sc m nf ncf mods) : PreStep m nf ncf mods sc m :=
  ⟨m.store.core, rfl, .refl _, h⟩

theorem step_coreModule {sc : Scope E} {m : Machine.Config E σ} {nf ncf : Nat}
    {mods : List E.Module} (h : PreInv sc m nf ncf mods) (mo : E.Module) :
    TOrT dispatch (instantiateDef R inst outer args sc (.coreModule mo)) m
      (PreStep m nf ncf (mods ++ [mo])) := by
  rw [instDef_coreModuleG]
  exact TOrT.runs (TRuns.pure _ m) (preStep_refl
    ⟨h.funcs_len, h.funcs_ok, h.coreFuncs_len, by simp [h.mods], h.lock⟩)

theorem step_funcType {sc : Scope E} {m : Machine.Config E σ} {nf ncf : Nat}
    {mods : List E.Module} (h : PreInv sc m nf ncf mods) {ft : Syntax.FuncType}
    (hft : funcTypePrim ft = true) :
    TOrT dispatch (instantiateDef R inst outer args sc (.type (.func ft))) m
      (PreStep m nf ncf mods) := by
  obtain ⟨t, ht⟩ := resolveFuncType_prim sc.frame hft
  rw [instDef_funcTypeG sc ht]
  exact TOrT.runs (TRuns.pure _ m) (preStep_refl
    ⟨h.funcs_len, h.funcs_ok, h.coreFuncs_len, h.mods, h.lock⟩)

theorem step_import {sc : Scope E} {m : Machine.Config E σ} {nf ncf : Nat}
    {mods : List E.Module} (h : PreInv sc m nf ncf mods) (ha : ArgsOk args m)
    (n : Syntax.ExternName) (t : Nat) :
    TOrT dispatch (instantiateDef R inst outer args sc (.import_ n (.func t))) m
      (PreStep m (nf + 1) ncf mods) := by
  cases hl : args.lookup n.name with
  | none =>
    simp only [instantiateDef, hl, orTrap]
    exact TOrT.trap ((isSpecTrap_trap (r := .hostTrap _) (fun msg e => by cases e)).bind _)
  | some v =>
    obtain ⟨g, fi, rfl, hfi⟩ := ha _ _ hl
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
      refine TOrT.runs (TRuns.pure _ m) (preStep_refl ⟨?_, ?_, h.coreFuncs_len, h.mods, h.lock⟩)
      · simp [h.funcs_len]
      · intro g' hg'
        rcases List.mem_append.mp hg' with hg' | hg'
        · exact h.funcs_ok g' hg'
        · rw [List.mem_singleton.mp hg']
          exact ⟨fi, hfi⟩

theorem step_lower {sc : Scope E} {m : Machine.Config E σ} {nf ncf : Nat}
    {mods : List E.Module} (h : PreInv sc m nf ncf mods) {g : Nat} (hg : g < nf) :
    TOrT dispatch (instantiateDef R inst outer args sc (.canon (.lower g []))) m
      (PreStep m nf (ncf + 1) mods) := by
  have hg' : g < sc.frame.funcs.length := h.funcs_len ▸ hg
  obtain ⟨fi, hfi⟩ := h.funcs_ok _ (List.getElem_mem hg')
  have hr : resolveLower? sc.frame g [] = some (sc.frame.funcs[g], {}) := by
    simp only [resolveLower?, Frame.func?, List.getElem?_eq_getElem hg', resolveOpts?_nil]
    rfl
  simp only [instantiateDef, hr, need, orTrap, pure_bind, pushEntry, Frame.push]
  have ha := TRuns.allocCoreHostG (σ := σ) (CanonHost.lowered sc.frame.funcs[g] fi.ft {} inst) m
  refine TOrT.runs ((TRuns.getObjG ArenaField.funcs _ m hfi).bind (ha.bind (TRuns.pure _ _))) ?_
  · refine ⟨_, rfl, .step _ _ (.refl _), h.funcs_len, h.funcs_ok, ?_, h.mods, h.lock⟩
    simp [h.coreFuncs_len]

theorem step_exports {sc : Scope E} {m : Machine.Config E σ} {nf ncf : Nat}
    {mods : List E.Module} (h : PreInv sc m nf ncf mods)
    {items : List (String × Syntax.SortIdx Syntax.CoreSort)}
    (hi : items.all (fun p => p.2.sort == .func && decide (p.2.idx < ncf)) = true) :
    TOrT dispatch (instantiateDef R inst outer args sc (.coreInstance (.exports items))) m
      (PreStep m nf ncf mods) := by
  obtain ⟨es, hes⟩ := items_mapM (f := sc.frame) items (h.coreFuncs_len ▸ hi)
  simp only [instantiateDef, hes, need, orTrap, pure_bind, pushEntry, Frame.push]
  exact TOrT.runs (TRuns.pure _ m) (preStep_refl
    ⟨h.funcs_len, h.funcs_ok, h.coreFuncs_len, h.mods, h.lock⟩)

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem argsOk_core {m : Machine.Config E σ} (h : ArgsOk args m) (c : E.Store (CanonHost E)) :
    ArgsOk args { m with store := { m.store with core := c } } := h

/-- **The definitions before the first core instantiation** trap with a specification trap, or
run silently, only allocating host functions in the core store. -/
theorem prefix_run : ∀ (pre : List (Syntax.Definition E.Module)) (nf ncf : Nat)
    (sc : Scope E) (m : Machine.Config E σ) (mods : List E.Module), ArgsOk args m →
    preOk nf ncf pre = true → PreInv sc m nf ncf mods →
    TOrT dispatch (pre.foldlM (instantiateDef R inst outer args) sc) m
      (PreOut m (mods ++ coreMods pre))
  | [], nf, ncf, sc, m, mods, _, _, h =>
    TOrT.runs (TRuns.pure _ m) ⟨m.store.core, nf, ncf, rfl, .refl _, by simpa [coreMods] using h⟩
  | d :: ds, nf, ncf, sc, m, mods, ha, hp, h => by
    rw [List.foldlM_cons]
    have cont : ∀ nf' ncf' mods', preOk nf' ncf' ds = true → mods' ++ coreMods ds = mods ++ coreMods (d :: ds) →
        ∀ sc' m', PreStep m nf' ncf' mods' sc' m' →
          TOrT dispatch (ds.foldlM (instantiateDef R inst outer args) sc') m'
            (PreOut m (mods ++ coreMods (d :: ds))) := by
      rintro nf' ncf' mods' hp' hmods sc' m' ⟨c', rfl, hc', hinv⟩
      refine (prefix_run ds nf' ncf' sc' _ mods' (argsOk_core ha c') hp' hinv).mono ?_
      rintro sc'' m'' ⟨c'', nf'', ncf'', rfl, hc'', hinv''⟩
      exact ⟨c'', nf'', ncf'', rfl, hc'.trans hc'', hmods ▸ hinv''⟩
    match d, hp with
    | .coreModule mo, hp =>
      exact (step_coreModule h mo).bind (cont nf ncf _ hp (by simp [coreMods]))
    | .type (.func ft), hp =>
      simp only [preOk, Bool.and_eq_true] at hp
      exact (step_funcType h hp.1).bind (cont nf ncf _ hp.2 (by simp [coreMods]))
    | .import_ n (.func t), hp =>
      exact (step_import h ha n t).bind (cont (nf + 1) ncf _ hp (by simp [coreMods]))
    | .canon (.lower g []), hp =>
      simp only [preOk, Bool.and_eq_true, decide_eq_true_eq] at hp
      exact (step_lower h hp.1).bind (cont nf (ncf + 1) _ hp.2 (by simp [coreMods]))
    | .coreInstance (.exports items), hp =>
      simp only [preOk, Bool.and_eq_true] at hp
      exact (step_exports h hp.1).bind (cont nf ncf _ hp.2 (by simp [coreMods]))

end Fold

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
