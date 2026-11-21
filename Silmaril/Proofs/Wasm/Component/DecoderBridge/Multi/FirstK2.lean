module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.FirstK
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Nodes
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.LaterCore

/-!
# The first node, with the frame related to the symbolic reading

`firstK' : FirstK'`: `FirstK` (`Multi.FirstK.firstK`), and the frame at the definitions after
the first core instantiation has the index spaces of the symbolic reading (`refStep`) of the
definitions up to and including it (`FrameRel`):

* `FrameTy sc sc' fs`: the frame of `sc'` has the types of `sc` and the resolutions of the
  primitive function types `fs` (`TyEntry`), the component functions and exports of `sc`;
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

/-- The function types defined by `ds`, in order. -/
def synTypes {M : Type} : List (Syntax.Definition M) → List Syntax.FuncType
  | [] => []
  | .type (.func f) :: ds => f :: synTypes ds
  | _ :: ds => synTypes ds

theorem synTypes_length {M : Type} (ds : List (Syntax.Definition M)) :
    (synTypes ds).length = nTypes ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    by_cases h : ∃ f, d = .type (.func f)
    · obtain ⟨f, rfl⟩ := h
      simp [synTypes, nTypes, ih]
    · have h' : ∀ f, d = .type (.func f) → False := fun f hf => h ⟨f, hf⟩
      rw [synTypes.eq_3 _ _ h', nTypes.eq_3 _ _ h', ih]

/-- A frame type entry: the resolution of the primitive function type `f`. -/
def TyEntry (f : Syntax.FuncType) (x : Types.TypeDef RtId E.ExternType) : Prop :=
  funcTypePrim f = true ∧ ∃ (fr : Frame E) (t : Types.FuncType RtId), resolveFuncType? fr f = some t ∧
    x = .func t

theorem tyEntry_func {fs : List Syntax.FuncType} {ts : List (Types.TypeDef RtId E.ExternType)}
    (h : List.Forall₂ TyEntry fs ts) : ∀ x ∈ ts, ∃ t, x = .func t := by
  induction h with
  | nil => simp
  | cons hp _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨-, _, t, -, rfl⟩ := hp
      exact ⟨t, rfl⟩
    · exact ih x hx

/-- The frame of `sc'` has the types of `sc` followed by the resolutions of `fs`, and the
component functions and exports of `sc`. -/
def FrameTy (sc sc' : Scope E) (fs : List Syntax.FuncType) : Prop :=
  (∃ ts, sc'.frame.types = sc.frame.types ++ ts ∧ List.Forall₂ TyEntry fs ts) ∧
    sc'.frame.funcs = sc.frame.funcs ∧ sc'.exports = sc.exports

theorem FrameTy.nil {sc sc' : Scope E} (ht : sc'.frame.types = sc.frame.types)
    (hf : sc'.frame.funcs = sc.frame.funcs) (he : sc'.exports = sc.exports) : FrameTy sc sc' [] :=
  ⟨⟨[], by simp [ht], .nil⟩, hf, he⟩

theorem FrameTy.trans {sc sc₁ sc₂ : Scope E} {fs fs' : List Syntax.FuncType}
    (h₁ : FrameTy sc sc₁ fs) (h₂ : FrameTy sc₁ sc₂ fs') : FrameTy sc sc₂ (fs ++ fs') := by
  obtain ⟨⟨ts, h1, h3⟩, h4, h5⟩ := h₁
  obtain ⟨⟨ts', h1', h3'⟩, h4', h5'⟩ := h₂
  exact ⟨⟨ts ++ ts', by rw [h1', h1, List.append_assoc], List.rel_append h3 h3'⟩, h4'.trans h4,
    h5'.trans h5⟩

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
      PreStepX g0 fx inst m nf ncf (mods ++ [mo]) insts sc' m' ∧ FrameTy sc sc' [] := by
  rw [instDef_coreModuleG]
  exact ⟨_, _, TRuns.pure _ m, preStepX_refl
    ⟨h.funcs_len, h.funcs_ok, h.coreFuncs_len, by simp [h.mods], h.lock⟩
    ⟨hx.funcs, hx.fxGet, hx.coreFuncs, hx.coreInsts, hx.core⟩, FrameTy.nil rfl rfl rfl⟩

theorem stepZ_funcType {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {nf ncf : Nat}
    {mods : List (core3 o).Module} {insts : List (List (String × Nat))}
    (h : PreInv sc m nf ncf mods) (hx : PreInvX g0 fx inst sc m ncf insts)
    {ft : Syntax.FuncType} (hft : funcTypePrim ft = true) :
    ∃ sc' m', TRuns (instantiateDef R inst outer args sc (.type (.func ft))) m sc' m' ∧
      PreStepX g0 fx inst m nf ncf mods insts sc' m' ∧ FrameTy sc sc' [ft] := by
  obtain ⟨t, ht⟩ := resolveFuncType_prim sc.frame hft
  rw [instDef_funcTypeG sc ht]
  exact ⟨_, _, TRuns.pure _ m, preStepX_refl
    ⟨h.funcs_len, h.funcs_ok, h.coreFuncs_len, h.mods, h.lock⟩
    ⟨hx.funcs, hx.fxGet, hx.coreFuncs, hx.coreInsts, hx.core⟩,
    ⟨⟨[.func t], rfl, .cons ⟨hft, sc.frame, t, ht, rfl⟩ .nil⟩, rfl, rfl⟩⟩

theorem stepZ_lower {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {nf ncf : Nat}
    {mods : List (core3 o).Module} {insts : List (List (String × Nat))}
    (h : PreInv sc m nf ncf mods) (hx : PreInvX g0 fx inst sc m ncf insts)
    (hty : ∀ at_, (CanonHost.lowered g0 fx.ft {} inst : CanonHost (core3 o)).coreType at_ =
      Param.v1Type fFlat)
    {g : Nat} (hg : g < nf) :
    ∃ sc' m', TRuns (instantiateDef R inst outer args sc (.canon (.lower g []))) m sc' m' ∧
      PreStepX g0 fx inst m nf (ncf + 1) mods insts sc' m' ∧ FrameTy sc sc' [] := by
  have hg' : g < sc.frame.funcs.length := h.funcs_len ▸ hg
  have hgg : sc.frame.funcs[g] = g0 := hx.funcs _ (List.getElem_mem hg')
  have hr : resolveLower? sc.frame g [] = some (sc.frame.funcs[g], {}) := by
    simp only [resolveLower?, Frame.func?, List.getElem?_eq_getElem hg', resolveOpts?_nil]
    rfl
  simp only [instantiateDef, hr, need, orTrap, pure_bind, pushEntry, Frame.push]
  rw [hgg]
  have ha := TRuns.allocCoreHostG (σ := σ) (CanonHost.lowered g0 fx.ft {} inst) m
  refine ⟨_, _, (TRuns.getObjG ArenaField.funcs _ m hx.fxGet).bind (ha.bind (TRuns.pure _ _)),
    ?_, FrameTy.nil rfl rfl rfl⟩
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
        FrameTy sc sc' [] := by
  have hes := items_mapM_val hx.coreFuncs items hi
  simp only [instantiateDef, hes, need, orTrap, pure_bind, pushEntry, Frame.push]
  refine ⟨_, _, TRuns.pure _ m, preStepX_refl
    ⟨h.funcs_len, h.funcs_ok, h.coreFuncs_len, h.mods, h.lock⟩
    ⟨hx.funcs, hx.fxGet, hx.coreFuncs, ?_, hx.core⟩, FrameTy.nil rfl rfl rfl⟩
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
        sc' m' ∧ FrameTy sc sc' (synTypes pre)
  | [], nf, ncf, sc, m, mods, insts, _, _, h, hx =>
    ⟨sc, m, TRuns.pure _ m, ⟨m.store.core, nf, ncf, rfl, by simpa [coreMods] using h,
      preInvX_core (by simpa [preLowers, preInsts] using hx) _ rfl⟩, FrameTy.nil rfl rfl rfl⟩
  | d :: ds, nf, ncf, sc, m, mods, insts, hp, hni, h, hx => by
    rw [List.foldlM_cons]
    have hni' : noImport ds = true := by
      simp only [noImport, List.all_cons, Bool.and_eq_true] at hni
      exact hni.2
    have cont : ∀ nf' ncf' mods' insts' k, preOk nf' ncf' ds = true →
        mods' ++ coreMods ds = mods ++ coreMods (d :: ds) →
        ncf' + preLowers ds = ncf + preLowers (d :: ds) →
        insts' ++ preInsts ds = insts ++ preInsts (d :: ds) → k ++ synTypes ds = synTypes (d :: ds) →
        ∀ sc₁ m₁, TRuns (instantiateDef R inst outer args sc d) m sc₁ m₁ →
          PreStepX g0 fx inst m nf' ncf' mods' insts' sc₁ m₁ → FrameTy sc sc₁ k →
          ∃ sc' m', TRuns (instantiateDef R inst outer args sc d >>= fun sc =>
              ds.foldlM (instantiateDef R inst outer args) sc) m sc' m' ∧
            PreOutX g0 fx inst m (mods ++ coreMods (d :: ds)) (ncf + preLowers (d :: ds))
              (insts ++ preInsts (d :: ds)) sc' m' ∧ FrameTy sc sc' (synTypes (d :: ds)) := by
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
      exact cont nf ncf _ insts [] hp (by simp [coreMods]) (by simp [preLowers])
        (by simp [preInsts]) (by simp [synTypes])
        sc₁ m₁ h₁ hs.1 hs.2
    | .type (.func ft), hp =>
      simp only [preOk, Bool.and_eq_true] at hp
      obtain ⟨sc₁, m₁, h₁, hs⟩ := stepZ_funcType (R := R) (outer := outer) (args := args) h hx hp.1
      exact cont nf ncf _ insts [ft] hp.2 (by simp [coreMods]) (by simp [preLowers])
        (by simp [preInsts]) (by simp [synTypes]) sc₁ m₁ h₁ hs.1 hs.2
    | .import_ n (.func t), hp =>
      simp [noImport] at hni
    | .canon (.lower g []), hp =>
      simp only [preOk, Bool.and_eq_true, decide_eq_true_eq] at hp
      obtain ⟨sc₁, m₁, h₁, hs⟩ := stepZ_lower (R := R) (outer := outer) (args := args) h hx hty hp.1
      exact cont nf (ncf + 1) _ insts [] hp.2 (by simp [coreMods]) (by simp [preLowers]; omega)
        (by simp [preInsts]) (by simp [synTypes]) sc₁ m₁ h₁ hs.1 hs.2
    | .coreInstance (.exports items), hp =>
      simp only [preOk, Bool.and_eq_true] at hp
      obtain ⟨sc₁, m₁, h₁, hs⟩ := stepZ_exports (R := R) (outer := outer) (args := args) h hx hp.1
      exact cont nf ncf _ _ [] hp.2 (by simp [coreMods]) (by simp [preLowers])
        (by simp [preInsts]) (by simp [synTypes])
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
      sc'.frame.funcs.length = 1 ∧ sc'.exports = [] ∧
      List.Forall₂ TyEntry (synTypes pre) sc'.frame.types := by
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
  obtain ⟨sc', m', hrun, ⟨c', nf', ncf', rfl, hinv, hinvx⟩, ⟨⟨ts, hts, hTS⟩, hfn, hex⟩⟩ :=
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
    by rw [hinvx.coreFuncs, Nat.zero_add]; rfl, hinvx.coreInsts.trans rfl, ?_, ?_, ?_, hex, ?_⟩
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
  case refine_4 =>
    rw [hts]
    exact .cons ⟨rfl, Frame.empty, tX, resolve_fFuncType, rfl⟩ hTS
  case refine_1 =>
    have htl : ts.length = nTypes pre' := hTS.length_eq.symm.trans (synTypes_length _)
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
    · exact tyEntry_func hTS x hx
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
    refine ⟨_, _, d.trans (.cons ⟨List.cons_ne_nil _ _, hl⟩ s (.refl _)), ?_, rfl, hl,
      rfl, rfl, ?_, rfl⟩
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

/-! ## The first node -/

local notation "Σh" => Unit × List HLinked2.HostEvent

/-- **The first node with a finishing continuation, the machine invariant, and the frame
related to the symbolic reading.** -/
theorem firstK_failFrag : FirstKAt MultiImpFailFrag := by
  intro b c r p ps t₀ pre mi cargs post hc hr hf himp hn hu hq hs
  obtain ⟨hfi, hw, -, pre₁, mi₁, cargs₁, post₁, hs₁, hshape, hpostOk⟩ := multiImpFailFrag_inv hf
  rw [hs] at hs₁
  obtain ⟨rfl, rfl, rfl, rfl⟩ : pre = pre₁ ∧ mi = mi₁ ∧ cargs = cargs₁ ∧ post = post₁ := by
    simp only [Option.some.injEq, Prod.mk.injEq] at hs₁
    exact ⟨hs₁.1, hs₁.2.1, hs₁.2.2.1, hs₁.2.2.2⟩
  have hpostNI := noImport_of_postOk hpostOk
  obtain ⟨pre', post', mi', cargs', m, hs', hpre, hm, hlen, hlow, hrt, hmod, himps, hilen, hwl, hw',
    hnames⟩ := firstImp_setup hc hr hw hfi himp hn
  rw [hs] at hs'
  simp only [Option.some.injEq, Prod.mk.injEq] at hs'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
  obtain ⟨ys, hEI, hF⟩ := hq
  obtain ⟨hlog, hans⟩ := coreLog_eq hw' hwl hF hu
  change EngineInst (core3P (profile neverFail))
    (Param.instOfI (core3P (profile neverFail)) (Binary.coreModule p.1) (CoreModule.imports p.1)
      (CoreModule.exports p.1)) (CoreModule.imports p.1) ys _ at hEI
  rw [hmod] at hEI
  obtain ⟨-, hsome⟩ := instOfI_cases himps hnames
  obtain ⟨J, hJ, hstart⟩ := hEI
  obtain ⟨mi₂, hp⟩ := hsome J hJ
  rw [hilen] at hp
  -- the root, up to the first core instantiation
  obtain ⟨sc', Kr, hF', hKF, hfm, hcfs, hfi', htyl, htyf, hfnl, -, -⟩ :=
    root_firstK2 hs hpre hshape hpostNI
  obtain ⟨tr₁, -, d₁⟩ := hF' (fun _ => pure .unit) [] [] rfl
  generalize hK : (fun b => Kr b >>= fun _ => pure Ret.unit) = K at d₁
  have hKF' : KFin K := hK ▸ hKF
  let M₁ : Machine.Config (core3 neverFail) Σh := lowCfg hostConfigX (preLowers pre) lowH
  have hcore : M₁.store.core = lowStore m.imports.length lowH := by
    show lowStore (preLowers pre) lowH = _
    rw [hlen]
  have hmd : sc'.frame.coreModule? mi = some m := by
    simp only [Frame.coreModule?, hfm]
    exact hm
  have hci := coreImportsFor_low (o := neverFail) (h := lowH) (md := m) hfi' hlow hrt
  rw [← hcore] at hci
  cases hv : Silmaril.Wasm.Validation.validate? m with
  | none =>
    exfalso
    unfold Core3.prepareE? at hp
    rw [hv] at hp
    cases hp
  | some mt =>
  rw [importTypesE_length hv] at hci
  have hsh := prepareE_mapH (fun _ : Nat => lowH) (irStore m.imports.length) m
    ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func)
  rw [mapH_irStore, ← hcore] at hsh
  have hpr : (core3 neverFail).prepare? M₁.store.core m
      ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) =
      some (Store.mapH gL J.store, mi₂, J.start) :=
    hsh.trans (by rw [hp]; rfl)
  have hready : HostReadyCfg hostConfigX := ⟨rfl, rfl, rfl⟩
  -- the frame after the first core instantiation and the symbolic reading
  have hFR : ∀ R₀, (pre ++ [Syntax.Definition.coreInstance (.instantiate mi cargs)]).foldlM refStep
      ({ env := (r.filter isFuncImport).length } : RSt) = some R₀ →
      FrameRel (coreMods pre) R₀ ({ sc' with frame := { sc'.frame with
        coreInstances := sc'.frame.coreInstances ++ [(core3 neverFail).exports mi₂] } } :
          Scope (core3 neverFail)) := by
    intro R₀ hR₀
    rw [List.foldlM_append] at hR₀
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, List.foldlM_cons, List.foldlM_nil]
      at hR₀
    obtain ⟨R, hR, hR'⟩ := hR₀
    have hR'' : refStep R (.coreInstance (.instantiate mi cargs)) = some R₀ := by
      simpa using hR'
    exact frameRel_inst (frameRel_root hshape hpre hR htyl htyf hfnl hcfs hfi') hR'' hm rfl rfl
      rfl rfl (prepareE?_exportsS hpr)
  -- the typing of the core store after the preparation, and its trampolines
  have hsOk₀ : Silmaril.Wasm.Execution.Core.StoreOk
      (Store.mapH gL (irStore m.imports.length)) := by
    rw [mapH_irStore]
    exact storeOk_lowStore _ _
  have hp₀ := prepareE_mapH gL (irStore m.imports.length) m
    ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func)
  rw [hp] at hp₀
  obtain ⟨hsJ, -, ⟨newJ, hnewJ, hwasmJ⟩, -⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed hsOk₀ hp₀
  have hHT : HostTy (Store.mapH gL J.store) := by
    intro fi hfi h hcode
    rw [hnewJ, mapH_irStore] at hfi
    rcases List.mem_append.mp hfi with hfi | hfi
    · simp only [lowStore, List.mem_replicate] at hfi
      rw [hfi.2]
      rfl
    · obtain ⟨c, hc⟩ := hwasmJ fi hfi
      rw [hc] at hcode
      cases hcode
  have htramp : ∀ i, i < preLowers pre →
      (Store.mapH gL J.store).funcs[i]? = some (lowFI lowH) := by
    intro i hi
    rw [hnewJ, mapH_irStore, List.getElem?_append_left (by simp [lowStore]; omega)]
    simp [lowStore, show i < m.imports.length by omega]
  -- the program at the first core instantiation
  have hX : (List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc'
      (Syntax.Definition.coreInstance (.instantiate mi cargs) :: post) >>= K) =
      (instantiateCore ⟨0⟩ sc'.frame mi cargs >>= fun es =>
        (pushEntry sc'.frame (.core .instance_) (.coreInstance es) >>= fun f =>
          pure ({ sc' with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
        List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc post >>= K) := by
    erw [List.foldlM_cons]
    simp only [instantiateDef, bind_assoc]
  erw [hX] at d₁
  -- the core instance on the frame, then the definitions after it
  have hpush : ∀ (es : List (String × (core3 neverFail).ExternVal)) (m₂ : Machine.Config (core3 neverFail) Σh),
      RunsQ (DG embL.host) none (pushEntry sc'.frame (.core .instance_) (.coreInstance es) >>= fun f =>
        pure ({ sc' with frame := f } : Scope (core3 neverFail))) m₂ []
        ({ sc' with frame := { sc'.frame with coreInstances := sc'.frame.coreInstances ++ [es] } } :
          Scope (core3 neverFail)) m₂ := by
    intro es m₂
    simp only [pushEntry, need, orTrap, Frame.push, pure_bind]
    exact .pure _ _
  -- the final configuration is at the definitions after the first core instantiation
  have finish : ∀ (tr : List (Label (core3 neverFail) Σh)) (M : Machine.Config (core3 neverFail) Σh)
      (sc : Scope (core3 neverFail)),
      LRun first.prof embL.hr (DG embL.host)
        { hostConfigX with ctl := ⟨none, .prog (instantiateProg r (importArgs hostI) >>=
          fun _ => pure .unit), []⟩ :: [] } tr
        { M with ctl := ⟨none, .prog (List.foldlM (instantiateDef callRecurse ⟨0⟩ []
          (importArgs hostI)) sc post >>= K), []⟩ :: [] } →
      M.store.lockdown = false → M.host = ((), logOfCalls t₀) → LaterInv pre sc M →
      (∀ R₀, (pre ++ [Syntax.Definition.coreInstance (.instantiate mi cargs)]).foldlM refStep
        ({ env := (r.filter isFuncImport).length } : RSt) = some R₀ →
        FrameRel (coreMods pre) R₀ sc) →
      ∃ sc M, RefAtDefsK r post sc (logOfCalls t₀) M ∧ LaterInv pre sc M ∧
        ∀ R₀, (pre ++ [Syntax.Definition.coreInstance (.instantiate mi cargs)]).foldlM refStep
          ({ env := (r.filter isFuncImport).length } : RSt) = some R₀ →
          FrameRel (coreMods pre) R₀ sc := by
    intro tr M sc d hl hh hinv hfr
    refine ⟨sc, _, ⟨⟨tr, d, Adequacy.LRun.no_host d,
      fun msg => Adequacy.LRun.no_trap d ⟨List.cons_ne_nil _ _, hl⟩ _⟩, ⟨K, hKF', rfl⟩, hl, hh⟩,
      ?_⟩
    exact ⟨⟨hinv.mods, hinv.insts, hinv.lock, hinv.func0, hinv.inst, hinv.tramp, hinv.ok,
      hinv.hosts, hinv.depth⟩, hfr⟩
  rcases hstart with ⟨hnone, rfl⟩ | ⟨f, c', fvs, hfs, hrun, hst⟩
  · -- no start function
    have ht₀ : t₀ = [] := by cases hF; rfl
    subst ht₀
    rw [hnone] at hpr
    have hcore' : ∀ M : Machine.Config (core3 neverFail) Σh, M.store = M₁.store →
        RunsQ (DG embL.host) none (instantiateCore ⟨0⟩ sc'.frame mi cargs) M
        [.tau, .tau] ((core3 neverFail).exports mi₂)
        { M with store := setCoreSt (Store.mapH gL J.store) M.store } := by
      intro M hM
      unfold instantiateCore
      simp only [hmd, need, orTrap]
      refine RunsQ.bind (tr₁ := []) (.pure _ _) ?_
      refine RunsQ.bind (tr₁ := [.tau]) (.get (.pure _ _)) ?_
      have hci' := hci
      have hpr' := hpr
      rw [← hM] at hci' hpr'
      rw [hci']
      refine RunsQ.bind (tr₁ := []) (.pure _ _) ?_
      erw [hpr']
      exact RunsQ.bind (tr₁ := [.tau])
        (.modify (f := setCoreSt (E := core3 neverFail) (Store.mapH gL J.store)) rfl (.pure _ _))
        (.pure _ _)
    have d₂ := RunsQ.lrun_at (prof := first.prof) (hr := embL.hr) (RunsQ.bind (f := fun es =>
          pushEntry sc'.frame (.core .instance_) (.coreInstance es) >>= fun f =>
            pure ({ sc' with frame := f } : Scope (core3 neverFail))) (hcore' { M₁ with ctl :=
          ⟨none, .prog (instantiateCore ⟨0⟩ sc'.frame mi cargs >>= fun es =>
          (pushEntry sc'.frame (.core .instance_) (.coreInstance es) >>= fun f =>
            pure ({ sc' with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
          List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
            (post : List (Syntax.Definition (core3 neverFail).Module)) >>= K), []⟩ :: [] } rfl)
          (hpush _ _))
        (show M₁.store.lockdown = false from rfl)
        (fun sc => List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
          (post : List (Syntax.Definition (core3 neverFail).Module)) >>= K) (segs := []) (rest := [])
        (by simp only [bind_assoc])
    refine finish _ _ _ (d₁.trans d₂) rfl rfl ⟨by simpa using hfm,
      ⟨[(core3 neverFail).exports mi₂], by simp only [hfi']; rfl⟩, rfl,
      rfl, ⟨{}, rfl, .inl rfl⟩, htramp, hsJ, hHT, rfl⟩ hFR
  · -- a start function
    rw [hfs] at hpr
    have hrun' : Param.StartRunI (core3P (profile neverFail)) (CoreModule.imports p.1)
        (J.store, Silmaril.Wasm.SingleThreaded.Thread.invoke f []) ys c' := hrun
    -- the core instantiation, up to its start call
    have hR : Reaches first.prof embL.hr (DG embL.host) none
        (Instantiate.runStart ⟨0⟩ f) (instantiateCore ⟨0⟩ sc'.frame mi cargs) M₁
        ([] ++ ([.tau] ++ ([] ++ ([.tau] ++ []))))
        { M₁ with store := setCoreSt (Store.mapH gL J.store) M₁.store }
        (fun m₂ tr' a m' => RunsQ (DG embL.host) none
          ((fun _ => pure ((core3 neverFail).exports mi₂)) ()) m₂ tr' a m') := by
      unfold instantiateCore
      simp only [hmd, need, orTrap]
      refine Reaches.seq (tr₁ := []) (.pure _ _) ?_
      refine Reaches.seq (tr₁ := [.tau]) (.get (.pure _ _)) ?_
      rw [hci]
      refine Reaches.seq (tr₁ := []) (.pure _ _) ?_
      erw [hpr]
      refine Reaches.seq (tr₁ := [.tau])
        (.modify (f := setCoreSt (E := core3 neverFail) (Store.mapH gL J.store)) rfl (.pure _ _)) ?_
      exact Reaches.here _ _
    obtain ⟨K', d₂, hK'⟩ := hR (fun es =>
        (pushEntry sc'.frame (.core .instance_) (.coreInstance es) >>= fun f =>
          pure ({ sc' with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
        List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
          (post : List (Syntax.Definition (core3 neverFail).Module)) >>= K) [] [] rfl
    -- the start call, to the core activation
    obtain ⟨ι', hadd, hrem⟩ : ∃ ι', ({} : InstState).addThread? ⟨0⟩ = some (1, ι') ∧
        ι'.removeThread? 1 = some (⟨0⟩, InstState.removeThread 1 ι') := ⟨_, rfl, rfl⟩
    obtain ⟨M₀, thc, Kc, segsc, restc, tr₃, d₃, hob₃, hS⟩ := start_atG (impl := embL.host) first.prof
      { ({ M₁ with store := setCoreSt (Store.mapH gL J.store) M₁.store } :
          Machine.Config (core3 neverFail) Σh) with
        ctl := ⟨none, .prog (Instantiate.runStart ⟨0⟩ f >>= K'), []⟩ :: [] }
      f {} ι' rfl rfl rfl hadd hrem
    have hml : ι'.mayLeave = true := by
      unfold InstState.addThread? at hadd
      obtain ⟨⟨i, tb⟩, -, he⟩ := Option.map_eq_some_iff.mp hadd
      cases he
      rfl
    have hB : CallInv M₀ thc := by
      have hth₀ := hS.thread
      subst hth₀
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hS.store]; rfl
      · rw [hS.store]; rfl
      · rw [hS.store]; exact ⟨ι', rfl, hml⟩
      · rw [hS.store]; rfl
    -- the typing of the start thread
    have hsOk : Silmaril.Wasm.Execution.Core.StoreOk (Store.mapH gL (irStore m.imports.length)) := by
      rw [mapH_irStore]
      exact storeOk_lowStore _ _
    have hp' := prepareE_mapH gL (irStore m.imports.length) m
      ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func)
    rw [hp, hfs] at hp'
    obtain ⟨hs', -, ⟨new, hnew, hwasm⟩, hcfg⟩ :=
      Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed hsOk hp'
    have hRT : RT (Store.mapH gL J.store) (Silmaril.Wasm.SingleThreaded.Thread.invoke f []) := by
      refine ⟨hs', hcfg f rfl, fun fi hfi h hcode => ?_⟩
      rw [hnew, mapH_irStore] at hfi
      rcases List.mem_append.mp hfi with hfi | hfi
      · simp only [lowStore, List.mem_replicate] at hfi
        rw [hfi.2]
        rfl
      · obtain ⟨c, hc⟩ := hwasm fi hfi
        rw [hc] at hcode
        cases hcode
    have hM₀ : coreCfg M₀ thc Kc segsc restc
        (Store.mapH gL J.store, Silmaril.Wasm.SingleThreaded.Thread.invoke f []) = M₀ := by
      have e := coreCfg_self hS.ctl
      have hco : M₀.store.core = Store.mapH gL J.store := by rw [hS.store]; rfl
      rw [hco] at e
      exact e
    -- the start run with its host calls
    obtain ⟨tr₄, B', tR', d₄, hob₄, hst', hB', hhost, hExt, hRT'⟩ := startRun_refX (prof := first.prof)
      (K := Kc) (segs := segsc) (rest := restc) himps hrun' hans hst hB
      (tR := Silmaril.Wasm.SingleThreaded.Thread.invoke f []) rfl hRT
    rw [hM₀] at d₄
    -- no values
    have hfv : fvs = [] := by
      have := Silmaril.Wasm.Component.Engine.Core3.Typed.returned_typed (o := neverFail) (rs := [])
        ⟨hRT'.store, fun fi hfi h hc => ⟨_, hRT'.hosts fi hfi h hc⟩⟩ hRT'.thread hst'
      simpa using this
    subst hfv
    have d₅ := retStep (th := thc) (K := Kc) (segs := segsc) (rest := restc)
      (y := (Store.mapH gL c'.1, tR')) hst' hB'.lock
    -- the epilogue
    obtain ⟨h, xs, cs, rfl⟩ := hExt
    obtain ⟨tr₆, d₆, hob₆⟩ := hS.ret (Store.mapH gL c'.1, tR') h xs cs
    -- back in the core instantiation, then the core instance on the frame
    obtain ⟨d₇, -⟩ := hK' (startedCfgG embL.host { ({ M₁ with store := setCoreSt (Store.mapH gL J.store) M₁.store } :
          Machine.Config (core3 neverFail) Σh) with
          ctl := ⟨none, .prog (Instantiate.runStart ⟨0⟩ f >>= K'), []⟩ :: [] }
          f ι' (Store.mapH gL c'.1) h xs cs) [] ((core3 neverFail).exports mi₂) _ (.pure _ _) rfl
    have d₈ := RunsQ.lrun_at (prof := first.prof) (hr := embL.hr) (hpush ((core3 neverFail).exports mi₂)
        { startedCfgG embL.host { ({ M₁ with store := setCoreSt (Store.mapH gL J.store) M₁.store } :
          Machine.Config (core3 neverFail) Σh) with
          ctl := ⟨none, .prog (Instantiate.runStart ⟨0⟩ f >>= K'), []⟩ :: [] }
          f ι' (Store.mapH gL c'.1) h xs cs with
          ctl := ⟨none, .prog ((pushEntry sc'.frame (.core .instance_)
            (.coreInstance ((core3 neverFail).exports mi₂)) >>= fun f =>
              pure ({ sc' with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
            List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
              (post : List (Syntax.Definition (core3 neverFail).Module)) >>= K), []⟩ :: [] })
      (show _ = false from rfl)
      (fun sc => List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
        (post : List (Syntax.Definition (core3 neverFail).Module)) >>= K) (segs := []) (rest := [])
      rfl
    refine finish _ _ _ (d₁.trans (d₂.trans (d₃.trans (d₄.trans (d₅.trans (d₆.trans
      (d₇.trans d₈))))))) rfl ?_ ?_ hFR
    case refine_2 =>
      have hfc : (Store.mapH gL c'.1).funcs = (Store.mapH gL J.store).funcs := by
        simp only [Store.mapH, startRunI_funcs hrun']
      refine ⟨by simpa using hfm, ⟨[(core3 neverFail).exports mi₂], by simp only [hfi']; rfl⟩, rfl, rfl,
        ⟨ι₁, by rw [← removeThread_ι₁ hadd]; rfl, .inr rfl⟩, fun i hi => ?_, hRT'.store,
        hRT'.hosts, rfl⟩
      show (Store.mapH gL c'.1).funcs[i]? = _
      rw [hfc]
      exact htramp i hi
    show h = _
    have hh : h = (M₀.host.1, M₀.host.2 ++ coreLog ys) := hhost
    rw [hh, hS.host, hlog]
    rfl

theorem firstK' : FirstK' := by
  intro b c r p ps trace pre mi args post hc hr hfrag
  exact firstK_failFrag b c r p ps trace pre mi args post hc hr (multiImpFailFrag_of_multiImpFrag hfrag)

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
