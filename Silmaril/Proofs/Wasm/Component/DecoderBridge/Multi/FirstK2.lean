module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.FirstK
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Nodes

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

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
