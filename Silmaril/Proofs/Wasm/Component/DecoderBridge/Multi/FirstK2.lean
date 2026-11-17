module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.FirstK
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Nodes
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.LaterCore

/-!
# The first node, with the frame related to the symbolic reading

`firstK' : FirstK'`: `FirstK` (`Multi.FirstK.firstK`), and the frame at the definitions after
the first core instantiation has the index spaces of the symbolic reading (`refStep`) of the
definitions up to and including it (`FrameRel`):

* `FrameTy sc sc' k`: the frame of `sc'` has the types of `sc` and `k` more function types, and
  the component functions of `sc`;
* `stepZ_*`, `prefix_runZ`: `Multi.Root.stepY_*`, `prefix_runY` with `FrameTy`;
* `refFold_pre`: the symbolic reading of the definitions before the first core instantiation;
* `root_firstK2`: `Multi.RootK.root_firstK` with the frame's types and component functions;
* `prepareE?_exportsS`: the exports of a prepared instance, with or without segments.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Games Silmaril.Games.Inst
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
  Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (GrowOracle Internal status neverFail profile)

/-- The number of function type definitions. -/
def nTypes {M : Type} : List (Syntax.Definition M) → Nat
  | [] => 0
  | .type (.func _) :: ds => nTypes ds + 1
  | _ :: ds => nTypes ds

/-! ## The frame's types and component functions -/

section FrameTy

variable {E : CoreEngine}

/-- The frame of `sc'` has the types of `sc` followed by `k` function types, and the component
functions of `sc`. -/
def FrameTy (sc sc' : Scope E) (k : Nat) : Prop :=
  (∃ ts, sc'.frame.types = sc.frame.types ++ ts ∧ ts.length = k ∧ ∀ x ∈ ts, ∃ t, x = .func t) ∧
    sc'.frame.funcs = sc.frame.funcs

theorem FrameTy.nil {sc sc' : Scope E} (ht : sc'.frame.types = sc.frame.types)
    (hf : sc'.frame.funcs = sc.frame.funcs) : FrameTy sc sc' 0 :=
  ⟨⟨[], by simp [ht], rfl, by simp⟩, hf⟩

theorem FrameTy.trans {sc sc₁ sc₂ : Scope E} {k k' : Nat} (h₁ : FrameTy sc sc₁ k)
    (h₂ : FrameTy sc₁ sc₂ k') : FrameTy sc sc₂ (k + k') := by
  obtain ⟨⟨ts, h1, h2, h3⟩, h4⟩ := h₁
  obtain ⟨⟨ts', h1', h2', h3'⟩, h4'⟩ := h₂
  refine ⟨⟨ts ++ ts', by rw [h1', h1, List.append_assoc], by simp [h2, h2'], fun x hx => ?_⟩,
    h4'.trans h4⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact h3 x hx
  · exact h3' x hx

end FrameTy

/-! ## The definitions before the first core instantiation, with the frame -/

variable {o : GrowOracle} {σ : Type}

section Defs

variable {R : Recurse (core3 o) σ} {inst : InstId} {outer : List (Frame (core3 o))}
  {args : Exports (core3 o)} {g0 : FuncId} {fx : CFuncInst (core3 o)}

theorem stepZ_coreModule {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {nf ncf : Nat}
    {mods : List (core3 o).Module} {insts : List (List (String × Nat))}
    (h : PreInv sc m nf ncf mods) (hx : PreInvX g0 fx inst sc m ncf insts)
    (mo : (core3 o).Module) :
    ∃ sc' m', TRuns (instantiateDef R inst outer args sc (.coreModule mo)) m sc' m' ∧
      PreStepX g0 fx inst m nf ncf (mods ++ [mo]) insts sc' m' ∧ FrameTy sc sc' 0 := by
  rw [instDef_coreModuleG]
  exact ⟨_, _, TRuns.pure _ m, preStepX_refl
    ⟨h.funcs_len, h.funcs_ok, h.coreFuncs_len, by simp [h.mods], h.lock⟩
    ⟨hx.funcs, hx.fxGet, hx.coreFuncs, hx.coreInsts, hx.core⟩, FrameTy.nil rfl rfl⟩

theorem stepZ_funcType {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {nf ncf : Nat}
    {mods : List (core3 o).Module} {insts : List (List (String × Nat))}
    (h : PreInv sc m nf ncf mods) (hx : PreInvX g0 fx inst sc m ncf insts)
    {ft : Syntax.FuncType} (hft : funcTypePrim ft = true) :
    ∃ sc' m', TRuns (instantiateDef R inst outer args sc (.type (.func ft))) m sc' m' ∧
      PreStepX g0 fx inst m nf ncf mods insts sc' m' ∧ FrameTy sc sc' 1 := by
  obtain ⟨t, ht⟩ := resolveFuncType_prim sc.frame hft
  rw [instDef_funcTypeG sc ht]
  exact ⟨_, _, TRuns.pure _ m, preStepX_refl
    ⟨h.funcs_len, h.funcs_ok, h.coreFuncs_len, h.mods, h.lock⟩
    ⟨hx.funcs, hx.fxGet, hx.coreFuncs, hx.coreInsts, hx.core⟩,
    ⟨⟨[.func t], rfl, rfl, by simp⟩, rfl⟩⟩

theorem stepZ_lower {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {nf ncf : Nat}
    {mods : List (core3 o).Module} {insts : List (List (String × Nat))}
    (h : PreInv sc m nf ncf mods) (hx : PreInvX g0 fx inst sc m ncf insts)
    (hty : ∀ at_, (CanonHost.lowered g0 fx.ft {} inst : CanonHost (core3 o)).coreType at_ =
      Param.v1Type fFlat)
    {g : Nat} (hg : g < nf) :
    ∃ sc' m', TRuns (instantiateDef R inst outer args sc (.canon (.lower g []))) m sc' m' ∧
      PreStepX g0 fx inst m nf (ncf + 1) mods insts sc' m' ∧ FrameTy sc sc' 0 := by
  have hg' : g < sc.frame.funcs.length := h.funcs_len ▸ hg
  have hgg : sc.frame.funcs[g] = g0 := hx.funcs _ (List.getElem_mem hg')
  have hr : resolveLower? sc.frame g [] = some (sc.frame.funcs[g], {}) := by
    simp only [resolveLower?, Frame.func?, List.getElem?_eq_getElem hg', resolveOpts?_nil]
    rfl
  simp only [instantiateDef, hr, need, orTrap, pure_bind, pushEntry, Frame.push]
  rw [hgg]
  have ha := TRuns.allocCoreHostG (σ := σ) (CanonHost.lowered g0 fx.ft {} inst) m
  refine ⟨_, _, (TRuns.getObjG ArenaField.funcs _ m hx.fxGet).bind (ha.bind (TRuns.pure _ _)),
    ?_, FrameTy.nil rfl rfl⟩
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

theorem stepZ_exports {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {nf ncf : Nat}
    {mods : List (core3 o).Module} {insts : List (List (String × Nat))}
    (h : PreInv sc m nf ncf mods) (hx : PreInvX g0 fx inst sc m ncf insts)
    {items : List (String × Syntax.SortIdx Syntax.CoreSort)}
    (hi : items.all (fun p => p.2.sort == .func && decide (p.2.idx < ncf)) = true) :
    ∃ sc' m', TRuns (instantiateDef R inst outer args sc (.coreInstance (.exports items))) m
        sc' m' ∧
      PreStepX g0 fx inst m nf ncf mods (insts ++ [items.map fun p => (p.1, p.2.idx)]) sc' m' ∧
        FrameTy sc sc' 0 := by
  have hes := items_mapM_val hx.coreFuncs items hi
  simp only [instantiateDef, hes, need, orTrap, pure_bind, pushEntry, Frame.push]
  refine ⟨_, _, TRuns.pure _ m, preStepX_refl
    ⟨h.funcs_len, h.funcs_ok, h.coreFuncs_len, h.mods, h.lock⟩
    ⟨hx.funcs, hx.fxGet, hx.coreFuncs, ?_, hx.core⟩, FrameTy.nil rfl rfl⟩
  show sc.frame.coreInstances ++ [_] = _
  rw [hx.coreInsts]
  simp only [instsVal, List.map_append, List.map_cons, List.map_nil, List.map_map]
  rfl

end Defs

section Fold

variable {R : Recurse (core3 o) σ} {inst : InstId} {outer : List (Frame (core3 o))}
  {args : Exports (core3 o)} {g0 : FuncId} {fx : CFuncInst (core3 o)}

/-- **The definitions before the first core instantiation, without imports, run silently.** -/
theorem prefix_runZ (hty : ∀ at_, (CanonHost.lowered g0 fx.ft {} inst : CanonHost (core3 o)).coreType
      at_ = Param.v1Type fFlat) :
    ∀ (pre : List (Syntax.Definition (core3 o).Module)) (nf ncf : Nat)
    (sc : Scope (core3 o)) (m : Machine.Config (core3 o) σ) (mods : List (core3 o).Module)
    (insts : List (List (String × Nat))),
    preOk nf ncf pre = true → noImport pre = true → PreInv sc m nf ncf mods →
    PreInvX g0 fx inst sc m ncf insts →
    ∃ sc' m', TRuns (pre.foldlM (instantiateDef R inst outer args) sc) m sc' m' ∧
      PreOutX g0 fx inst m (mods ++ coreMods pre) (ncf + preLowers pre) (insts ++ preInsts pre)
        sc' m' ∧ FrameTy sc sc' (nTypes pre)
  | [], nf, ncf, sc, m, mods, insts, _, _, h, hx =>
    ⟨sc, m, TRuns.pure _ m, ⟨m.store.core, nf, ncf, rfl, by simpa [coreMods] using h,
      preInvX_core (by simpa [preLowers, preInsts] using hx) _ rfl⟩, FrameTy.nil rfl rfl⟩
  | d :: ds, nf, ncf, sc, m, mods, insts, hp, hni, h, hx => by
    rw [List.foldlM_cons]
    have hni' : noImport ds = true := by
      simp only [noImport, List.all_cons, Bool.and_eq_true] at hni
      exact hni.2
    have cont : ∀ nf' ncf' mods' insts' k, preOk nf' ncf' ds = true →
        mods' ++ coreMods ds = mods ++ coreMods (d :: ds) →
        ncf' + preLowers ds = ncf + preLowers (d :: ds) →
        insts' ++ preInsts ds = insts ++ preInsts (d :: ds) → k + nTypes ds = nTypes (d :: ds) →
        ∀ sc₁ m₁, TRuns (instantiateDef R inst outer args sc d) m sc₁ m₁ →
          PreStepX g0 fx inst m nf' ncf' mods' insts' sc₁ m₁ → FrameTy sc sc₁ k →
          ∃ sc' m', TRuns (instantiateDef R inst outer args sc d >>= fun sc =>
              ds.foldlM (instantiateDef R inst outer args) sc) m sc' m' ∧
            PreOutX g0 fx inst m (mods ++ coreMods (d :: ds)) (ncf + preLowers (d :: ds))
              (insts ++ preInsts (d :: ds)) sc' m' ∧ FrameTy sc sc' (nTypes (d :: ds)) := by
      rintro nf' ncf' mods' insts' k hp' hmods hncf hinsts hk sc₁ m₁ h₁ ⟨c', rfl, hinv, hinvx⟩ hT₁
      obtain ⟨sc', m', h₂, ⟨c'', nf'', ncf'', rfl, hinv'', hinvx''⟩, hT₂⟩ :=
        prefix_runZ hty ds nf' ncf' sc₁ _ mods' insts' hp' hni' hinv hinvx
      refine ⟨sc', _, h₁.bind h₂, ⟨c'', nf'', ncf'', rfl, hmods ▸ hinv'', ?_⟩, ?_⟩
      · rw [← hncf, ← hinsts]
        exact ⟨hinvx''.funcs, hinvx''.fxGet, hinvx''.coreFuncs, hinvx''.coreInsts, hinvx''.core⟩
      · rw [← hk]
        exact hT₁.trans hT₂
    match d, hp with
    | .coreModule mo, hp =>
      obtain ⟨sc₁, m₁, h₁, hs⟩ := stepZ_coreModule (R := R) (outer := outer) (args := args) h hx mo
      exact cont nf ncf _ insts 0 hp (by simp [coreMods]) (by simp [preLowers])
        (by simp [preInsts]) (by simp [nTypes])
        sc₁ m₁ h₁ hs.1 hs.2
    | .type (.func ft), hp =>
      simp only [preOk, Bool.and_eq_true] at hp
      obtain ⟨sc₁, m₁, h₁, hs⟩ := stepZ_funcType (R := R) (outer := outer) (args := args) h hx hp.1
      exact cont nf ncf _ insts 1 hp.2 (by simp [coreMods]) (by simp [preLowers])
        (by simp [preInsts]) (by simp [nTypes]; omega) sc₁ m₁ h₁ hs.1 hs.2
    | .import_ n (.func t), hp =>
      simp [noImport] at hni
    | .canon (.lower g []), hp =>
      simp only [preOk, Bool.and_eq_true, decide_eq_true_eq] at hp
      obtain ⟨sc₁, m₁, h₁, hs⟩ := stepZ_lower (R := R) (outer := outer) (args := args) h hx hty hp.1
      exact cont nf (ncf + 1) _ insts 0 hp.2 (by simp [coreMods]) (by simp [preLowers]; omega)
        (by simp [preInsts]) (by simp [nTypes]) sc₁ m₁ h₁ hs.1 hs.2
    | .coreInstance (.exports items), hp =>
      simp only [preOk, Bool.and_eq_true] at hp
      obtain ⟨sc₁, m₁, h₁, hs⟩ := stepZ_exports (R := R) (outer := outer) (args := args) h hx hp.1
      exact cont nf ncf _ _ 0 hp.2 (by simp [coreMods]) (by simp [preLowers])
        (by simp [preInsts]) (by simp [nTypes])
        sc₁ m₁ h₁ hs.1 hs.2

end Fold

/-! ## The symbolic reading before the first core instantiation -/

section Read

/-- An inline core instance of the reading and the frame's. -/
theorem inline_rel (M : List Silmaril.Wasm.Module) {cf : List Impl} :
    ∀ {items : List (String × Syntax.SortIdx Syntax.CoreSort)} {es : List (String × Impl)},
      items.mapM (fun (p : String × Syntax.SortIdx Syntax.CoreSort) =>
        if p.2.sort = .func then (cf[p.2.idx]?).map ((p.1, ·)) else none) = some es →
      CIRel M (.inline es) ((items.map fun p => (p.1, p.2.idx)).map
        fun p => (p.1, Silmaril.Wasm.Execution.Core.ExternAddr.func p.2))
  | [], es, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    intro n hn
    simp at hn
  | p :: items, es, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, es', hes', rfl⟩ := h
    have ih := inline_rel M hes'
    have hx1 : x.1 = p.1 := by
      split at hx
      · obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.mp hx
        rfl
      · cases hx
    intro n hn
    obtain ⟨x1, x2⟩ := x
    simp only at hx1
    subst hx1
    simp only [List.map_cons, List.lookup_cons] at hn ⊢
    cases hb : n == p.1
    · rw [hb] at hn
      exact ih n hn
    · exact ⟨_, rfl⟩

/-- **The symbolic reading of the definitions before the first core instantiation** (without
imports): the modules, the function types and the core functions are appended, the component
functions kept, and the inline core instances appended, related to the frame's. -/
theorem refFold_pre (M : List Silmaril.Wasm.Module) :
    ∀ (pre : List (Syntax.Definition Silmaril.Wasm.Module)) (nf ncf : Nat) (R R' : RSt),
      preOk nf ncf pre = true → noImport pre = true → pre.foldlM refStep R = some R' →
      R'.mods = R.mods ++ coreMods pre ∧ R'.types.length = R.types.length + nTypes pre ∧
      R'.funcs.length = R.funcs.length ∧
      R'.coreFuncs.length = R.coreFuncs.length + preLowers pre ∧
      ∃ X, R'.coreInsts = R.coreInsts ++ X ∧
        List.Forall₂ (fun ci its => CIRel M ci (its.map
          fun p => (p.1, Silmaril.Wasm.Execution.Core.ExternAddr.func p.2))) X (preInsts pre)
  | [], _, _, R, R', _, _, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨by simp [coreMods], by simp [nTypes], rfl, by simp [preLowers], [], by simp,
      by simp [preInsts]⟩
  | d :: ds, nf, ncf, R, R', hp, hni, h => by
    have hni' : noImport ds = true := by
      simp only [noImport, List.all_cons, Bool.and_eq_true] at hni
      exact hni.2
    simp only [List.foldlM_cons] at h
    cases hR : refStep R d with
    | none => rw [hR] at h; cases h
    | some R₁ =>
    rw [hR] at h
    match d, hp, hR with
    | .coreModule mo, hp, hR =>
      simp only [refStep, Option.some.injEq] at hR
      subst hR
      obtain ⟨h1, h2, h3, h4, X, h5, h6⟩ := refFold_pre M ds nf ncf _ R' hp hni' h
      exact ⟨by simp [h1, coreMods], by simp [h2, nTypes], h3, by simp [h4, preLowers], X,
        by simpa using h5, by simpa [preInsts] using h6⟩
    | .type (.func ft), hp, hR =>
      simp only [preOk, Bool.and_eq_true] at hp
      simp only [refStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hR
      obtain ⟨ft', -, rfl⟩ := hR
      obtain ⟨h1, h2, h3, h4, X, h5, h6⟩ := refFold_pre M ds nf ncf _ R' hp.2 hni' h
      exact ⟨by simp [h1, coreMods], by simp [h2, nTypes]; omega, h3,
        by simp [h4, preLowers], X, by simpa using h5, by simpa [preInsts] using h6⟩
    | .canon (.lower g []), hp, hR =>
      simp only [preOk, Bool.and_eq_true, decide_eq_true_eq] at hp
      simp only [refStep, Option.bind_eq_bind, Option.bind_eq_some_iff] at hR
      obtain ⟨⟨im, ft⟩, -, hR⟩ := hR
      split at hR
      · cases hR
      · simp only [Option.some.injEq] at hR
        subst hR
        obtain ⟨h1, h2, h3, h4, X, h5, h6⟩ := refFold_pre M ds nf (ncf + 1) _ R' hp.2 hni' h
        exact ⟨by simp [h1, coreMods], by simp [h2, nTypes], h3,
          by simp [h4, preLowers]; omega, X, by simpa using h5, by simpa [preInsts] using h6⟩
    | .coreInstance (.exports items), hp, hR =>
      simp only [preOk, Bool.and_eq_true] at hp
      simp only [refStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hR
      obtain ⟨es, hes, rfl⟩ := hR
      obtain ⟨h1, h2, h3, h4, X, h5, h6⟩ := refFold_pre M ds nf ncf _ R' hp.2 hni' h
      refine ⟨by simp [h1, coreMods], by simp [h2, nTypes], h3, by simp [h4, preLowers],
        .inline es :: X, by simp [h5], ?_⟩
      simp only [preInsts]
      exact .cons (inline_rel M hes) h6
    | .import_ n (.func t), _, _ => simp [noImport] at hni

end Read

/-! ## The root, with the frame -/

section RootRun

/-- **Root instantiation up to the first core instantiation, with its continuation**: as
`root_firstY`, the continuation `Kr` of the definitions kept, which finishes the instantiation
(`KFin`) once the host's instantiation program ends. -/
theorem root_firstK2 {r pre post : Core3Component} {mi : Nat} {cargs : List (String × Nat)}
    (hs : firstCore? r = some (pre, mi, cargs, post)) (hpre : preOk 0 0 pre = true)
    (hshape : rootShape pre = true) (hpost : noImport post = true) :
    ∃ (sc' : Scope (core3 neverFail))
      (Kr : Scope (core3 neverFail) → Canon.P (core3 neverFail) (Unit × List HLinked2.HostEvent)
        (Ret (core3 neverFail))),
      FocusAtK first.prof embL.hr (DG embL.host) none
        ((Syntax.Definition.coreInstance (.instantiate mi cargs) :: post).foldlM
          (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc')
        (instantiateProg r (importArgs hostI)) hostConfigX
        (lowCfg hostConfigX (preLowers pre) lowH) Kr ∧
      KFin (fun sc => Kr sc >>= fun _ => pure .unit) ∧
      sc'.frame.coreModules = coreMods pre ∧ sc'.frame.coreFuncs = List.range (preLowers pre) ∧
      sc'.frame.coreInstances = instsVal (preInsts pre) ∧
      sc'.frame.types.length = nTypes pre ∧ (∀ x ∈ sc'.frame.types, ∃ t, x = .func t) ∧
      sc'.frame.funcs.length = 1 := by
  have hrr := firstCore?_eq r hs
  obtain ⟨pre', rfl, hni⟩ := rootShape_inv hshape
  have hrest : NoImport (pre' ++ Syntax.Definition.coreInstance (.instantiate mi cargs) :: post) :=
    (noImport_prop hni).append (noImport_cons_inst hpost)
  have hpre' : preOk 1 0 pre' = true := by
    simp only [preOk, Bool.and_eq_true] at hpre
    exact hpre.2
  have hr' : r = .type (.func fFuncType) :: .import_ { name := "f" } (.func 0) ::
      (pre' ++ Syntax.Definition.coreInstance (.instantiate mi cargs) :: post) := by
    rw [hrr]
    rfl
  have hpi : PreInv ({ frame := { frameT with funcs := [⟨0⟩] } } : Scope (core3 neverFail))
      rootCfg 1 0 [] :=
    ⟨rfl, fun g hg => by
      simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨_, rfl⟩, rfl, rfl, rfl⟩
  have hpx : PreInvX (⟨0⟩ : FuncId) (.host fWit ⟨0⟩) ⟨0⟩
      ({ frame := { frameT with funcs := [⟨0⟩] } } : Scope (core3 neverFail)) rootCfg 0 [] :=
    ⟨fun g hg => by simpa using hg, rfl, rfl, rfl, rfl⟩
  obtain ⟨sc', m', hrun, ⟨c', nf', ncf', rfl, hinv, hinvx⟩, ⟨⟨ts, hts, htl, htf⟩, hfn⟩⟩ :=
    prefix_runZ (R := callRecurse) (outer := []) (args := importArgs hostI) coreType_lowH pre' 1 0
      _ rootCfg [] [] hpre' hni hpi hpx
  have hc : c' = lowStore (preLowers (.type (.func fFuncType) ::
      .import_ { name := "f" } (.func 0) :: pre')) lowH := by
    have := hinvx.core
    rw [Nat.zero_add] at this
    exact this
  subst hc
  refine ⟨sc', ?_⟩
  apply Exists.intro
  refine ⟨?focus, ?fin, hinv.mods.trans rfl,
    by rw [hinvx.coreFuncs, Nat.zero_add]; rfl, hinvx.coreInsts.trans rfl, ?_, ?_, ?_⟩
  case focus =>
    unfold instantiateProg
    apply FocusAtK.silent (TRuns.modifyStore (f := DispatchSt.incNestingSt) (fun _ => rfl) _)
    apply FocusAtK.left
    unfold instantiateRootCall instantiateRoot
    rw [hr']
    erw [argsComplete_root hrest]
    apply FocusAtK.silent (TRuns.pure () _)
    apply FocusAtK.silent (TRuns.getStore _)
    rw [show ({ hostConfigX with store := DispatchSt.incNestingSt hostConfigX.store } :
        Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent)).store = preStore from rfl]
    erw [precheck_root hrest]
    apply FocusAtK.silent (TRuns.pure () _)
    apply FocusAtK.silent (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} _)
    apply FocusAtK.left
    unfold instantiateComponent
    apply FocusAtK.left
    dsimp only
    show FocusAtK first.prof embL.hr (DG embL.host) none _
      (List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI))
        ({} : Scope (core3 neverFail))
        (((.type (.func fFuncType) :: .import_ { name := "f" } (.func 0) ::
          (pre' ++ Syntax.Definition.coreInstance (.instantiate mi cargs) :: post))) :
          List (Syntax.Definition (core3 neverFail).Module))) _ _ _
    have ht : TRuns (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)
        ({} : Scope (core3 neverFail)) (.type (.func fFuncType))) rootCfg
        ({ frame := frameT } : Scope (core3 neverFail)) rootCfg := by
      rw [instDef_funcTypeG _ resolve_fFuncType]
      exact TRuns.pure _ _
    rw [List.foldlM_cons]
    apply FocusAtK.silent ht
    erw [List.foldlM_cons]
    apply FocusAtK.silent import_runs
    erw [List.foldlM_append]
    apply FocusAtK.silent hrun
    exact FocusAtK.self _ _
  case refine_1 =>
    rw [hts, List.length_append, htl]
    show 1 + _ = _
    rw [Nat.add_comm]
    rfl
  case refine_2 =>
    intro x hx
    rw [hts] at hx
    rcases List.mem_append.mp hx with hx | hx
    · simp [frameT] at hx
      exact ⟨_, hx⟩
    · exact htf x hx
  case refine_3 =>
    rw [hfn]
    rfl
  case fin =>
    intro sc M hl hc
    have hr1 : RunsQ (DG embL.host) none
        (modifyStore DispatchSt.decNestingSt >>= fun _ =>
          emit (instantiatedObs ⟨0⟩ (funcExports sc.exports)) >>= fun _ =>
            pure (Ret.unit : Ret (core3 neverFail)))
        M [.tau, .obs (instantiatedObs ⟨0⟩ (funcExports sc.exports))] Ret.unit
        { M with store := DispatchSt.decNestingSt M.store } :=
      RunsQ.bind (tr₁ := [.tau]) (.modify rfl (.pure _ _))
        (RunsQ.bind (tr₁ := [.obs _]) (.emit (.pure _ _)) (.pure _ _))
    have d := RunsQ.lrun_at (prof := first.prof) (hr := embL.hr) hr1 hl (fun _ => pure Ret.unit)
      (segs := []) (rest := []) (by rw [hc]; rfl)
    have s : UniqueStep first.prof embL.hr (DG embL.host)
        { ({ M with store := DispatchSt.decNestingSt M.store } :
            Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent)) with
          ctl := [⟨none, .prog (pure (Ret.unit : Ret (core3 neverFail))), []⟩] } .tau
        { M with store := DispatchSt.decNestingSt M.store, ctl := [] } :=
      .of_prog rfl (fun _ _ e => by cases e) (.hostDone (r := .unit) (rest := []) rfl)
    refine ⟨_, _, (d.trans (.cons ⟨List.cons_ne_nil _ _, hl⟩ s (.refl _))).steps, ?_, rfl, hl,
      rfl, rfl, ?_⟩
    · intro ev hev
      simp at hev
    · simp only [traceObs, List.filterMap_append, List.filterMap_cons, Label.obs?,
        List.filterMap_nil, List.append_nil, List.findSome?_cons,
        decodeInstantiated?_instantiatedObs]

end RootRun

/-! ## The frame at the first core instantiation and the symbolic reading -/

section Rel

/-- **The symbolic reading of the definitions before the first core instantiation relates to the
root's frame.** -/
theorem frameRel_root {pre : RefComponent} {k : Nat} {R : RSt} {sc : Scope (core3 neverFail)}
    (hshape : rootShape pre = true) (hpre : preOk 0 0 pre = true)
    (hR : pre.foldlM refStep ({ env := k } : RSt) = some R)
    (hty : sc.frame.types.length = nTypes pre) (htf : ∀ x ∈ sc.frame.types, ∃ t, x = .func t)
    (hfn : sc.frame.funcs.length = 1) (hcf : sc.frame.coreFuncs = List.range (preLowers pre))
    (hci : sc.frame.coreInstances = instsVal (preInsts pre)) :
    FrameRel (coreMods pre) R sc := by
  obtain ⟨pre', rfl, hni⟩ := rootShape_inv hshape
  have hpre' : preOk 1 0 pre' = true := by
    simp only [preOk, Bool.and_eq_true] at hpre
    exact hpre.2
  simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at hR
  obtain ⟨R₁, h₁, R₂, h₂, hR⟩ := hR
  simp only [refStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₁
  obtain ⟨ft, -, rfl⟩ := h₁
  simp only [refStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₂
  obtain ⟨ft', -, rfl⟩ := h₂
  obtain ⟨h1, h2, h3, h4, X, h5, h6⟩ := refFold_pre (coreMods
    (.type (.func fFuncType) :: .import_ { name := "f" } (.func 0) :: pre')) pre' 1 0 _ R hpre'
    hni hR
  refine ⟨by simp [h1, coreMods], ?_, htf, ?_, ?_, ?_⟩
  · rw [hty, h2]
    simp only [nTypes, List.nil_append, List.length_singleton]
    omega
  · rw [hfn, h3]
    rfl
  · rw [hcf, h4]
    show (List.range _).length = _
    simp [preLowers]
  · rw [hci, h5]
    simp only [List.nil_append, preInsts, instsVal]
    exact List.forall₂_map_right_iff.mpr h6

/-- Segment initialisation keeps the frame. -/
theorem initSegments?_frame {H : Type} {s s' : Silmaril.Wasm.Execution.Core.Store H}
    {f f' : Silmaril.Wasm.Execution.Core.Frame} {m : Silmaril.Wasm.Module}
    (h : Silmaril.Wasm.Execution.Core.initSegments? Silmaril.Wasm.Execution.Core.evalConst? s f m =
      some (s', f')) : f' = f := by
  unfold Silmaril.Wasm.Execution.Core.initSegments? at h
  split at h
  · cases h
  rename_i s₁ f₁ he
  unfold Silmaril.Wasm.Execution.Core.initElem? at he
  unfold Silmaril.Wasm.Execution.Core.initData? at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at he h
  obtain ⟨-, -, -, rfl⟩ := he
  obtain ⟨-, -, -, rfl⟩ := h
  rfl

/-- **The exports of a prepared instance**, with or without segments. -/
theorem prepareE?_exportsS {H : Type} {s s' : Silmaril.Wasm.Execution.Core.Store H}
    {m : Silmaril.Wasm.Module} {xas : List Silmaril.Wasm.Execution.Core.ExternAddr}
    {i : Silmaril.Wasm.Execution.Core.ModuleInst} {st : Option Nat}
    (h : Silmaril.Wasm.Component.Engine.Core3.prepareE? s m xas = some (s', i, st)) :
    List.Forall₂ (fun (e : Silmaril.Wasm.Export) (x : String × (core3 neverFail).ExternVal) =>
        x.1 = e.name ∧ ∀ k, e.index = .func k →
          ∃ a : Nat, x.2 = Silmaril.Wasm.Execution.Core.ExternAddr.func a)
      m.exports ((core3 neverFail).exports i) := by
  obtain ⟨mt, f', st₀, -, -, hi, rfl, -⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_inv h
  have hE : List.Forall₂ ExpShape m.exports f'.module.exports := by
    unfold Silmaril.Wasm.Execution.Core.instantiateOnce? at hi
    split at hi
    · cases hi
    unfold Silmaril.Wasm.Execution.Core.instantiateDirect?
      Silmaril.Wasm.Execution.Core.prepareDirect? at hi
    split at hi
    · cases hi
    rename_i c st' hc
    split at hi
    · cases hi
    rename_i s₂ f₂ hseg
    simp only [Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨-, rfl, -⟩ := hi
    rw [initSegments?_frame hseg]
    exact prepare?_exports (m := m.globalResidue) hc
  show List.Forall₂ _ m.exports (f'.module.exports.map fun x => (x.name, x.addr))
  refine List.forall₂_map_right_iff.mpr (hE.imp fun e x hx => ⟨hx.1, fun k hk => ?_⟩)
  exact hx.2 k hk

end Rel

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
