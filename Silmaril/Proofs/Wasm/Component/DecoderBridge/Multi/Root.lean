module

public import Silmaril.Wasm.Component.DecoderBridge.Multi.Defs
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Main
public import Silmaril.Proofs.Wasm.Component.Reference.InstRun

/-!
# Root instantiation up to the first core instantiation, without a trap

`FirstImp.Root.root_firstX` reaches the first core instantiation **or** traps with a specification
trap (a failed root check or import check). On the fragment `MultiImpFrag` the definitions before
the first core instantiation start with the type `func(x: u32)` and the import `f` of it and
import nothing else (`rootShape`), so the checks are two closed computations on `hostConfigX`
(kernel-checked) and the rest of the walk cannot trap:

* `stepY_*`, `prefix_runY`: the definitions before the first core instantiation, other than
  imports, run silently (`TRuns`), with the invariants of `FirstImp.Prefix`;
* `root_firstY`: root instantiation of `r` from `hostConfigX` reaches, in every context, the
  definitions from the first core instantiation on (`(.coreInstance (.instantiate mi cargs) ::
  post).foldlM …`), in the configuration of the trampolines (`lowCfg`), with the frame's core
  modules, core functions and inline core instances those of the definitions before it.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

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
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (GrowOracle neverFail)

variable {o : GrowOracle} {σ : Type}

/-! ## The definitions before the first core instantiation, without imports -/

section Defs

variable {R : Recurse (core3 o) σ} {inst : InstId} {outer : List (Frame (core3 o))}
  {args : Exports (core3 o)} {g0 : FuncId} {fx : CFuncInst (core3 o)}

theorem stepY_coreModule {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {nf ncf : Nat}
    {mods : List (core3 o).Module} {insts : List (List (String × Nat))}
    (h : PreInv sc m nf ncf mods) (hx : PreInvX g0 fx inst sc m ncf insts)
    (mo : (core3 o).Module) :
    ∃ sc' m', TRuns (instantiateDef R inst outer args sc (.coreModule mo)) m sc' m' ∧
      PreStepX g0 fx inst m nf ncf (mods ++ [mo]) insts sc' m' := by
  rw [instDef_coreModuleG]
  exact ⟨_, _, TRuns.pure _ m, preStepX_refl
    ⟨h.funcs_len, h.funcs_ok, h.coreFuncs_len, by simp [h.mods], h.lock⟩
    ⟨hx.funcs, hx.fxGet, hx.coreFuncs, hx.coreInsts, hx.core⟩⟩

theorem stepY_funcType {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {nf ncf : Nat}
    {mods : List (core3 o).Module} {insts : List (List (String × Nat))}
    (h : PreInv sc m nf ncf mods) (hx : PreInvX g0 fx inst sc m ncf insts)
    {ft : Syntax.FuncType} (hft : funcTypePrim ft = true) :
    ∃ sc' m', TRuns (instantiateDef R inst outer args sc (.type (.func ft))) m sc' m' ∧
      PreStepX g0 fx inst m nf ncf mods insts sc' m' := by
  obtain ⟨t, ht⟩ := resolveFuncType_prim sc.frame hft
  rw [instDef_funcTypeG sc ht]
  exact ⟨_, _, TRuns.pure _ m, preStepX_refl
    ⟨h.funcs_len, h.funcs_ok, h.coreFuncs_len, h.mods, h.lock⟩
    ⟨hx.funcs, hx.fxGet, hx.coreFuncs, hx.coreInsts, hx.core⟩⟩

theorem stepY_lower {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {nf ncf : Nat}
    {mods : List (core3 o).Module} {insts : List (List (String × Nat))}
    (h : PreInv sc m nf ncf mods) (hx : PreInvX g0 fx inst sc m ncf insts)
    (hty : ∀ at_, (CanonHost.lowered g0 fx.ft {} inst : CanonHost (core3 o)).coreType at_ =
      Param.v1Type fFlat)
    {g : Nat} (hg : g < nf) :
    ∃ sc' m', TRuns (instantiateDef R inst outer args sc (.canon (.lower g []))) m sc' m' ∧
      PreStepX g0 fx inst m nf (ncf + 1) mods insts sc' m' := by
  have hg' : g < sc.frame.funcs.length := h.funcs_len ▸ hg
  have hgg : sc.frame.funcs[g] = g0 := hx.funcs _ (List.getElem_mem hg')
  have hr : resolveLower? sc.frame g [] = some (sc.frame.funcs[g], {}) := by
    simp only [resolveLower?, Frame.func?, List.getElem?_eq_getElem hg', resolveOpts?_nil]
    rfl
  simp only [instantiateDef, hr, need, orTrap, pure_bind, pushEntry, Frame.push]
  rw [hgg]
  have ha := TRuns.allocCoreHostG (σ := σ) (CanonHost.lowered g0 fx.ft {} inst) m
  refine ⟨_, _, (TRuns.getObjG ArenaField.funcs _ m hx.fxGet).bind (ha.bind (TRuns.pure _ _)), ?_⟩
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

theorem stepY_exports {sc : Scope (core3 o)} {m : Machine.Config (core3 o) σ} {nf ncf : Nat}
    {mods : List (core3 o).Module} {insts : List (List (String × Nat))}
    (h : PreInv sc m nf ncf mods) (hx : PreInvX g0 fx inst sc m ncf insts)
    {items : List (String × Syntax.SortIdx Syntax.CoreSort)}
    (hi : items.all (fun p => p.2.sort == .func && decide (p.2.idx < ncf)) = true) :
    ∃ sc' m', TRuns (instantiateDef R inst outer args sc (.coreInstance (.exports items))) m
        sc' m' ∧
      PreStepX g0 fx inst m nf ncf mods (insts ++ [items.map fun p => (p.1, p.2.idx)]) sc' m' := by
  have hes := items_mapM_val hx.coreFuncs items hi
  simp only [instantiateDef, hes, need, orTrap, pure_bind, pushEntry, Frame.push]
  refine ⟨_, _, TRuns.pure _ m, preStepX_refl
    ⟨h.funcs_len, h.funcs_ok, h.coreFuncs_len, h.mods, h.lock⟩
    ⟨hx.funcs, hx.fxGet, hx.coreFuncs, ?_, hx.core⟩⟩
  show sc.frame.coreInstances ++ [_] = _
  rw [hx.coreInsts]
  simp only [instsVal, List.map_append, List.map_cons, List.map_nil, List.map_map]
  rfl

end Defs

section Fold

variable {R : Recurse (core3 o) σ} {inst : InstId} {outer : List (Frame (core3 o))}
  {args : Exports (core3 o)} {g0 : FuncId} {fx : CFuncInst (core3 o)}

/-- **The definitions before the first core instantiation, without imports, run silently.** -/
theorem prefix_runY (hty : ∀ at_, (CanonHost.lowered g0 fx.ft {} inst : CanonHost (core3 o)).coreType
      at_ = Param.v1Type fFlat) :
    ∀ (pre : List (Syntax.Definition (core3 o).Module)) (nf ncf : Nat)
    (sc : Scope (core3 o)) (m : Machine.Config (core3 o) σ) (mods : List (core3 o).Module)
    (insts : List (List (String × Nat))),
    preOk nf ncf pre = true → noImport pre = true → PreInv sc m nf ncf mods →
    PreInvX g0 fx inst sc m ncf insts →
    ∃ sc' m', TRuns (pre.foldlM (instantiateDef R inst outer args) sc) m sc' m' ∧
      PreOutX g0 fx inst m (mods ++ coreMods pre) (ncf + preLowers pre) (insts ++ preInsts pre)
        sc' m'
  | [], nf, ncf, sc, m, mods, insts, _, _, h, hx =>
    ⟨sc, m, TRuns.pure _ m, m.store.core, nf, ncf, rfl, by simpa [coreMods] using h,
      preInvX_core (by simpa [preLowers, preInsts] using hx) _ rfl⟩
  | d :: ds, nf, ncf, sc, m, mods, insts, hp, hni, h, hx => by
    rw [List.foldlM_cons]
    have hni' : noImport ds = true := by
      simp only [noImport, List.all_cons, Bool.and_eq_true] at hni
      exact hni.2
    have cont : ∀ nf' ncf' mods' insts', preOk nf' ncf' ds = true →
        mods' ++ coreMods ds = mods ++ coreMods (d :: ds) →
        ncf' + preLowers ds = ncf + preLowers (d :: ds) →
        insts' ++ preInsts ds = insts ++ preInsts (d :: ds) →
        ∀ sc₁ m₁, TRuns (instantiateDef R inst outer args sc d) m sc₁ m₁ →
          PreStepX g0 fx inst m nf' ncf' mods' insts' sc₁ m₁ →
          ∃ sc' m', TRuns (instantiateDef R inst outer args sc d >>= fun sc =>
              ds.foldlM (instantiateDef R inst outer args) sc) m sc' m' ∧
            PreOutX g0 fx inst m (mods ++ coreMods (d :: ds)) (ncf + preLowers (d :: ds))
              (insts ++ preInsts (d :: ds)) sc' m' := by
      rintro nf' ncf' mods' insts' hp' hmods hncf hinsts sc₁ m₁ h₁ ⟨c', rfl, hinv, hinvx⟩
      obtain ⟨sc', m', h₂, c'', nf'', ncf'', rfl, hinv'', hinvx''⟩ :=
        prefix_runY hty ds nf' ncf' sc₁ _ mods' insts' hp' hni' hinv hinvx
      refine ⟨sc', _, h₁.bind h₂, c'', nf'', ncf'', rfl, hmods ▸ hinv'', ?_⟩
      rw [← hncf, ← hinsts]
      exact ⟨hinvx''.funcs, hinvx''.fxGet, hinvx''.coreFuncs, hinvx''.coreInsts, hinvx''.core⟩
    match d, hp with
    | .coreModule mo, hp =>
      obtain ⟨sc₁, m₁, h₁, hs⟩ := stepY_coreModule (R := R) (outer := outer) (args := args) h hx mo
      exact cont nf ncf _ insts hp (by simp [coreMods]) (by simp [preLowers]) (by simp [preInsts])
        sc₁ m₁ h₁ hs
    | .type (.func ft), hp =>
      simp only [preOk, Bool.and_eq_true] at hp
      obtain ⟨sc₁, m₁, h₁, hs⟩ := stepY_funcType (R := R) (outer := outer) (args := args) h hx hp.1
      exact cont nf ncf _ insts hp.2 (by simp [coreMods]) (by simp [preLowers])
        (by simp [preInsts]) sc₁ m₁ h₁ hs
    | .import_ n (.func t), hp =>
      simp [noImport] at hni
    | .canon (.lower g []), hp =>
      simp only [preOk, Bool.and_eq_true, decide_eq_true_eq] at hp
      obtain ⟨sc₁, m₁, h₁, hs⟩ := stepY_lower (R := R) (outer := outer) (args := args) h hx hty hp.1
      exact cont nf (ncf + 1) _ insts hp.2 (by simp [coreMods]) (by simp [preLowers]; omega)
        (by simp [preInsts]) sc₁ m₁ h₁ hs
    | .coreInstance (.exports items), hp =>
      simp only [preOk, Bool.and_eq_true] at hp
      obtain ⟨sc₁, m₁, h₁, hs⟩ := stepY_exports (R := R) (outer := outer) (args := args) h hx hp.1
      exact cont nf ncf _ _ hp.2 (by simp [coreMods]) (by simp [preLowers]) (by simp [preInsts])
        sc₁ m₁ h₁ hs

end Fold


/-! ## The root checks -/

section Root

theorem noImport_prop {M : Type} {ds : List (Syntax.Definition M)} (h : noImport ds = true) :
    NoImport ds := by
  intro d hd n x hx
  subst hx
  have := List.all_eq_true.mp h _ hd
  simp at this

/-- The shape `rootShape` asks for. -/
theorem rootShape_inv {M : Type} {pre : List (Syntax.Definition M)} (h : rootShape pre = true) :
    ∃ pre', pre = .type (.func fFuncType) :: .import_ { name := "f" } (.func 0) :: pre' ∧
      noImport pre' = true := by
  unfold rootShape at h
  split at h
  · rename_i ft n ds
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    exact ⟨ds, rfl, h⟩
  · cases h

/-- The function type `func(x: u32)`, resolved. -/
def tX : Types.FuncType RtId := { params := [("x", .prim .u32)], result := none }

theorem resolve_fFuncType :
    resolveFuncType? (Frame.empty : Frame (core3 neverFail)) fFuncType = some tX := rfl

/-- The frame after the type `func(x: u32)`. -/
def frameT : Frame (core3 neverFail) := { Frame.empty with types := [.func tX] }

theorem precheck_type (s : CStore (core3 neverFail)) (args : Exports (core3 neverFail)) :
    precheckDef s args Frame.empty (.type (.func fFuncType)) = .ok (some frameT) := rfl

/-- The store at the root's import pre-check. -/
abbrev preStore : CStore (core3 neverFail) := DispatchSt.incNestingSt hostConfigX.store

/-- The store at the root's definitions: the root instance allocated. -/
abbrev rootStore : CStore (core3 neverFail) :=
  ArenaOps.allocSt ArenaField.insts {} (DispatchSt.incNestingSt hostConfigX.store)

theorem check_pre : importTypeCheck preStore frameT "f" (.func 0) (.func ⟨0⟩) = .ok () := rfl

theorem check_root : importTypeCheck rootStore frameT "f" (.func 0) (.func ⟨0⟩) = .ok () := rfl

theorem lookup_f : (importArgs hostI : Exports (core3 neverFail)).lookup "f" = some (.func ⟨0⟩) :=
  rfl

theorem precheck_import :
    precheckDef preStore (importArgs hostI) frameT (.import_ { name := "f" } (.func 0)) =
      .ok (some frameT) := by
  simp only [precheckDef]
  rw [lookup_f]
  dsimp only
  rw [check_pre]
  rfl

theorem precheck_root {rest : List (Syntax.Definition (core3 neverFail).Module)}
    (h : NoImport rest) :
    precheckImports preStore (importArgs hostI) Frame.empty
      (.type (.func fFuncType) :: .import_ { name := "f" } (.func 0) :: rest) = .ok () := by
  simp only [precheckImports, precheck_type, precheck_import]
  exact precheckImports_ok _ _ _ _ h

theorem argsComplete_root {rest : List (Syntax.Definition (core3 neverFail).Module)}
    (h : NoImport rest) :
    argsComplete (.type (.func fFuncType) :: .import_ { name := "f" } (.func 0) :: rest)
      (importArgs hostI : Exports (core3 neverFail)) = true := by
  have hn := importNames_nil h
  simp only [argsComplete, importNames, List.filterMap_cons] at hn ⊢
  rw [hn]
  rfl

/-- The root's import, in the instantiation. -/
theorem import_runs :
    TRuns (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)
        ({ frame := frameT } : Scope (core3 neverFail)) (.import_ { name := "f" } (.func 0)))
      ({ hostConfigX with store := rootStore } :
        Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent))
      { frame := { frameT with funcs := [⟨0⟩] } } { hostConfigX with store := rootStore } := by
  simp only [instantiateDef]
  rw [show (importArgs hostI : Exports (core3 neverFail)).lookup ({ name := "f" } :
    Syntax.ExternName).name = some (.func ⟨0⟩) from rfl]
  simp only [orTrap, pure_bind]
  refine (TRuns.getStore _).bind ?_
  show TRuns (checkImport (importTypeCheck rootStore frameT "f" (.func 0) (.func ⟨0⟩)) >>= _) _ _ _
  rw [check_root]
  exact TRuns.pure _ _

end Root


/-! ## Root instantiation up to the first core instantiation -/

section RootRun

/-- The configuration of the root's definitions. -/
abbrev rootCfg : Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent) :=
  { hostConfigX with store := rootStore }

theorem noImport_cons_inst {mi : Nat} {cargs : List (String × Nat)}
    {post : List (Syntax.Definition (core3 neverFail).Module)} (h : noImport post = true) :
    NoImport (Syntax.Definition.coreInstance (.instantiate mi cargs) :: post) := by
  refine noImport_prop ?_
  simp only [noImport, List.all_cons, Bool.true_and]
  exact h

/-- **Root instantiation up to the first core instantiation, without a trap**: on `hostConfigX`
with the root arguments `importArgs hostI`, for a component whose definitions before the first
core instantiation have the shape `rootShape` and whose later definitions import nothing. -/
theorem root_firstY {r pre post : Core3Component} {mi : Nat} {cargs : List (String × Nat)}
    (hs : firstCore? r = some (pre, mi, cargs, post)) (hpre : preOk 0 0 pre = true)
    (hshape : rootShape pre = true) (hpost : noImport post = true) :
    ∃ sc' : Scope (core3 neverFail),
      FocusAt first.prof embL.hr (DG embL.host) none
        ((Syntax.Definition.coreInstance (.instantiate mi cargs) :: post).foldlM
          (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc')
        (instantiateProg r (importArgs hostI)) hostConfigX
        (lowCfg hostConfigX (preLowers pre) lowH) ∧
      sc'.frame.coreModules = coreMods pre ∧ sc'.frame.coreFuncs = List.range (preLowers pre) ∧
      sc'.frame.coreInstances = instsVal (preInsts pre) := by
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
  obtain ⟨sc', m', hrun, c', nf', ncf', rfl, hinv, hinvx⟩ :=
    prefix_runY (R := callRecurse) (outer := []) (args := importArgs hostI) coreType_lowH pre' 1 0
      _ rootCfg [] [] hpre' hni hpi hpx
  refine ⟨sc', ?_, hinv.mods.trans rfl, by rw [hinvx.coreFuncs, Nat.zero_add]; rfl, hinvx.coreInsts.trans rfl⟩
  have hc : c' = lowStore (preLowers (.type (.func fFuncType) ::
      .import_ { name := "f" } (.func 0) :: pre')) lowH := by
    have := hinvx.core
    rw [Nat.zero_add] at this
    exact this
  subst hc
  unfold instantiateProg
  refine FocusAt.silent (TRuns.modifyStore (f := DispatchSt.incNestingSt) (fun _ => rfl) _) ?_
  refine FocusAt.left ?_
  unfold instantiateRootCall instantiateRoot
  rw [hr']
  erw [argsComplete_root hrest]
  refine FocusAt.silent (TRuns.pure () _) ?_
  refine FocusAt.silent (TRuns.getStore _) ?_
  rw [show ({ hostConfigX with store := DispatchSt.incNestingSt hostConfigX.store } :
      Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent)).store = preStore from rfl]
  erw [precheck_root hrest]
  refine FocusAt.silent (TRuns.pure () _) ?_
  refine FocusAt.silent (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} _) ?_
  refine FocusAt.left ?_
  unfold instantiateComponent
  refine FocusAt.left ?_
  dsimp only
  show FocusAt first.prof embL.hr (DG embL.host) none _
    (List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) ({} : Scope (core3 neverFail))
      (((.type (.func fFuncType) :: .import_ { name := "f" } (.func 0) ::
        (pre' ++ Syntax.Definition.coreInstance (.instantiate mi cargs) :: post))) :
        List (Syntax.Definition (core3 neverFail).Module))) _ _
  have ht : TRuns (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI) ({} : Scope (core3 neverFail))
      (.type (.func fFuncType))) rootCfg ({ frame := frameT } : Scope (core3 neverFail)) rootCfg := by
    rw [instDef_funcTypeG _ resolve_fFuncType]
    exact TRuns.pure _ _
  rw [List.foldlM_cons]
  refine FocusAt.silent ht ?_
  erw [List.foldlM_cons]
  refine FocusAt.silent import_runs ?_
  erw [List.foldlM_append]
  refine FocusAt.silent hrun ?_
  exact FocusAt.self _ _

end RootRun

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
