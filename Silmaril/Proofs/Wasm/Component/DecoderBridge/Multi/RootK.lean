module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Later
public import Silmaril.Proofs.Wasm.Component.Reference.StartInst

/-!
# Root instantiation up to the first core instantiation, with its continuation

`Multi.Root.root_firstY` reaches the first core instantiation with the rest of the instantiation
program as an existential continuation. Here the continuation is kept:

* `FocusAtK th X p m m₁ K`: in every context `f`, the program `p` runs live from `m`, observing
  nothing, to `m₁` running `X` followed by `K` (then `f`); the combinators `here`, `left`, `seq`,
  `silent`;
* `root_firstK`: `root_firstY` with its continuation `Kr`, and `KFin` of `Kr` followed by the end
  of the host's instantiation program: from the scope of the finished definitions, the program
  pops the root result, decrements the nesting depth, observes the instantiation of instance `0`
  with the function exports of the scope, and returns to the host.
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

/-! ## Runs to a hole, with the continuation -/

section Focus

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

variable (prof hr dispatch) in
/-- In every context `f`, the program `p` runs live from `m`, observing nothing, to `m₁`, where
`X` runs, followed by `K` and `f`. -/
def FocusAtK (th : Option ThreadId) {β α : Type} (X : Canon.P E σ β) (p : Canon.P E σ α)
    (m m₁ : Machine.Config E σ) (K : β → Canon.P E σ α) : Prop :=
  ∀ (f : α → Canon.P E σ (Ret E)) (segs : List (Seg E σ)) (rest : List (Activation E σ)),
    m.store.lockdown = false →
    ∃ tr : List (Label E σ), traceObs tr = [] ∧
      LRun prof hr dispatch { m with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } tr
        { m₁ with ctl := ⟨th, .prog (X >>= fun b => K b >>= f), segs⟩ :: rest }

namespace FocusAtK

theorem here {th : Option ThreadId} {β α : Type} {X : Canon.P E σ β} (k : β → Canon.P E σ α)
    (m : Machine.Config E σ) : FocusAtK prof hr dispatch th X (X >>= k) m m k := by
  intro f segs rest _
  refine ⟨[], rfl, ?_⟩
  rw [bind_assoc]
  exact .refl _

theorem self {th : Option ThreadId} {β : Type} (X : Canon.P E σ β) (m : Machine.Config E σ) :
    FocusAtK prof hr dispatch th X X m m pure := by
  intro f segs rest _
  refine ⟨[], rfl, ?_⟩
  simp only [pure_bind]
  exact .refl _

theorem left {th : Option ThreadId} {β α γ : Type} {X : Canon.P E σ β} {p : Canon.P E σ γ}
    {g : γ → Canon.P E σ α} {m m₁ : Machine.Config E σ} {K : β → Canon.P E σ γ}
    (h : FocusAtK prof hr dispatch th X p m m₁ K) :
    FocusAtK prof hr dispatch th X (p >>= g) m m₁ (fun b => K b >>= g) := by
  intro f segs rest hl
  obtain ⟨tr, ho, r⟩ := h (fun b => g b >>= f) segs rest hl
  refine ⟨tr, ho, ?_⟩
  simp only [bind_assoc]
  exact r

theorem seq {th : Option ThreadId} {β α γ : Type} {X : Canon.P E σ β} {p : Canon.P E σ γ}
    {g : γ → Canon.P E σ α} {m m₁ m₂ : Machine.Config E σ} {tr₁ : List (Label E σ)} {c : γ}
    {K : β → Canon.P E σ α}
    (h₁ : RunsQ dispatch th p m tr₁ c m₁) (ho : traceObs tr₁ = [])
    (h₂ : FocusAtK prof hr dispatch th X (g c) m₁ m₂ K) :
    FocusAtK prof hr dispatch th X (p >>= g) m m₂ K := by
  intro f segs rest hl
  obtain ⟨tr, ho', r⟩ := h₂ f segs rest (h₁.lock.trans hl)
  refine ⟨tr₁ ++ tr, by simp only [traceObs, List.filterMap_append] at ho ho' ⊢; rw [ho, ho']; rfl, ?_⟩
  have d := h₁.lrun (prof := prof) (hr := hr) hl (fun b => g b >>= f) segs rest
  rw [bind_assoc]
  exact d.trans r

theorem silent {th : Option ThreadId} {β α γ : Type} {X : Canon.P E σ β} {p : Canon.P E σ γ}
    {g : γ → Canon.P E σ α} {m m₁ m₂ : Machine.Config E σ} {c : γ} {K : β → Canon.P E σ α}
    (h₁ : TRuns p m c m₁) (h₂ : FocusAtK prof hr dispatch th X (g c) m₁ m₂ K) :
    FocusAtK prof hr dispatch th X (p >>= g) m m₂ K := by
  obtain ⟨tr, hr₁, ho⟩ := SRuns.runsQO (dispatch := dispatch) h₁ th
  exact seq hr₁ ho h₂

end FocusAtK

end Focus

/-! ## The root, up to the first core instantiation -/

section RootRun

/-- **Root instantiation up to the first core instantiation, with its continuation**: as
`root_firstY`, the continuation `Kr` of the definitions kept, which finishes the instantiation
(`KFin`) once the host's instantiation program ends. -/
theorem root_firstK {r pre post : Core3Component} {mi : Nat} {cargs : List (String × Nat)}
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
  have hc : c' = lowStore (preLowers (.type (.func fFuncType) ::
      .import_ { name := "f" } (.func 0) :: pre')) lowH := by
    have := hinvx.core
    rw [Nat.zero_add] at this
    exact this
  subst hc
  refine ⟨sc', ?_⟩
  apply Exists.intro
  refine ⟨?focus, ?fin, hinv.mods.trans rfl,
    by rw [hinvx.coreFuncs, Nat.zero_add]; rfl, hinvx.coreInsts.trans rfl⟩
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

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
