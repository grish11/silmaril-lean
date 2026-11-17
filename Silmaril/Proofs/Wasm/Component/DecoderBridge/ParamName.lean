module

public import Silmaril.Wasm.Component.DecoderBridge.ParamName.Defs
public import Silmaril.Wasm.Component.DecoderBridge.Sem.Defs
public import Silmaril.Wasm.Component.InstTests.Thms
public import Silmaril.Wasm.Component.InstTestsRef.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.Main

/-!
# A parameter name the host does not have (proofs)

* `precheck_traps`: a root instantiation whose import pre-check fails traps with a
  specification trap (`TrapsQS`), over any engine;
* `not_instantiates_of_trapsQS`: **a root instantiation program that traps with a specification
  trap has no finishing run**: every run from the instantiation host event either stops inside
  the live run to the trap, or passes the trap, after which the store is locked down;
* `parse_paramName`, `decodeRef_paramName` (`kernel_rfl`), `paramName_valid` (`decide +kernel`
  on `check?`), `paramName_precheck` (`decide +kernel`): the two readings of `paramname.wasm`,
  the validity of the REF reading and the failing pre-check;
* `paramName_traps`, `paramName_not_instantiates`: under the logging host from `hostConfigX`,
  the reference machine's instantiation of `paramNameRef` traps, and no run finishes it;
* `not_startAdequacy`: hence `Task.startAdequacy` is false.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.ParamName

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Games Silmaril.Games.Inst
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
  Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (profile neverFail)

/-! ## Over any engine -/

section Generic

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)} [∀ a b, Decidable (E.ExternSub a b)]

/-- **A failing import pre-check traps**: the root instantiation of `r` traps with a
specification trap (`import type mismatch`, or `missing import` if an import is not supplied)
before any side effect. -/
theorem precheck_traps {m : Machine.Config E σ} {r : Syntax.Component E.Module}
    {args : Exports E} {e : String}
    (he : precheckImports (DispatchSt.incNestingSt m.store) args Frame.empty r = .error e) :
    ∃ tr mT, TrapsQS dispatch none (instantiateProg r args) m tr mT := by
  have h : TOrT dispatch (instantiateProg r args) m (fun _ _ => False) := by
    unfold instantiateProg
    refine TOrT.bind (TOrT.runs (TRuns.modifyStore (f := DispatchSt.incNestingSt) (fun _ => rfl) m)
      (Q := fun _ m' => m' = { m with store := DispatchSt.incNestingSt m.store }) rfl) ?_
    rintro _ m₁ rfl
    refine TOrT.bind (Q := fun _ _ => False) ?_ (fun _ _ h => h.elim)
    unfold instantiateRootCall instantiateRoot
    refine TOrT.bind (tOrT_trapIf (fun _ h => by cases h) _) ?_
    rintro _ m₂ rfl
    refine TOrT.bind (TOrT.runs (TRuns.getStore _)
      (Q := fun s m' => s = (DispatchSt.incNestingSt m.store : CStore E) ∧
        m' = { m with store := DispatchSt.incNestingSt m.store }) ⟨rfl, rfl⟩) ?_
    rintro s m₃ ⟨rfl, rfl⟩
    refine TOrT.bind (Q := fun _ _ => False) ?_ (fun _ _ h => h.elim)
    rw [he]
    exact TOrT.trap (isSpecTrap_trap (r := .hostTrap _) fun _ h => by cases h)
  rcases h with h | ⟨_, _, _, h⟩
  · exact h
  · exact h.elim

/-- **An instantiation program that traps has no finishing run.** -/
theorem not_instantiates_of_trapsQS {m : Machine.Config E σ} {c : Syntax.Component E.Module}
    {args : Exports E} {tr : List (Label E σ)} {mT : Machine.Config E σ} (hm : HostReadyCfg m)
    (h : TrapsQS dispatch none (instantiateProg c args) m tr mT) (m' : Machine.Config E σ)
    (inst : InstId) (es : List (String × FuncId)) :
    ¬ Instantiates prof hr dispatch m c args m' inst es := by
  rintro ⟨tr', hs, -, hc, hl, -⟩
  obtain ⟨q, segs', r, -, hrun, hlive, hu⟩ :=
    h.lrun (prof := prof) (hr := hr) hm.2.1 (fun _ => pure .unit) [] []
  cases hs with
  | cons s₀ hs =>
    cases s₀
    rcases hrun.inv hs with hlv | ⟨tr'', -, hs'⟩
    · exact hlv.1 hc
    · cases hs' with
      | refl => exact hlive.1 hc
      | cons s₁ hs₁ =>
        obtain ⟨-, rfl⟩ := hu.2 _ _ s₁
        have e₁ := steps_of_locked rfl (Adequacy.step_trap_lockdown hu.1) hs₁
        subst e₁
        rw [Adequacy.step_trap_lockdown hu.1] at hl
        cases hl

end Generic

/-! ## `paramname.wasm` -/

theorem parse_paramName : Binary.parseComponent paramNameBytes = .ok startsComp := by kernel_rfl

theorem decodeRef_paramName : decodeRef paramNameBytes = .ok paramNameRef := by kernel_rfl

theorem paramName_valid : ∃ ct, Valid Features.p2 paramNameRef ct := by
  have h : (check? Features.p2 paramNameRef).isOk = true := by decide +kernel
  cases e : check? Features.p2 paramNameRef with
  | error _ => rw [e] at h; cases h
  | ok ct => exact ⟨ct, check?_sound e⟩

theorem paramName_precheck_toBool :
    (precheckImports (DispatchSt.incNestingSt hostConfigX.store)
      (importArgs (E := core3 neverFail) hostI) Frame.empty paramNameRef).toBool = false := by
  decide +kernel

/-- **The reference machine's pre-check rejects the root import** (`f: func(y: u32)` against the
host function `f: func(x: u32)`). -/
theorem paramName_precheck : ∃ e,
    precheckImports (DispatchSt.incNestingSt hostConfigX.store)
      (importArgs (E := core3 neverFail) hostI) Frame.empty paramNameRef = .error e := by
  have h := paramName_precheck_toBool
  cases e : precheckImports (DispatchSt.incNestingSt hostConfigX.store)
      (importArgs (E := core3 neverFail) hostI) Frame.empty paramNameRef with
  | error e' => exact ⟨e', rfl⟩
  | ok _ => rw [e] at h; cases h

theorem paramName_trapsQS : ∃ tr mT,
    TrapsQS (DG embL.host) none (instantiateProg paramNameRef (importArgs hostI)) hostConfigX tr mT :=
  let ⟨_, he⟩ := paramName_precheck
  precheck_traps he

/-- **The reference instantiation of `paramNameRef` traps.** -/
theorem paramName_traps :
    InstResult.traps ∈
      instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX paramNameRef (importArgs hostI) := by
  have hready : HostReadyCfg hostConfigX := ⟨rfl, rfl, rfl⟩
  obtain ⟨tr, mT, ht⟩ := paramName_trapsQS
  exact instTraps_of_trapsQS (prof := first.prof) (hr := embL.hr) hready ht

/-- **No run finishes the reference instantiation of `paramNameRef`.** -/
theorem paramName_not_instantiates (M : Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent))
    (inst : InstId) (es : List (String × FuncId)) :
    ¬ Instantiates first.prof embL.hr (Host.ofEmbedder embL).dispatch hostConfigX paramNameRef
      (importArgs hostI) M inst es := by
  have hready : HostReadyCfg hostConfigX := ⟨rfl, rfl, rfl⟩
  obtain ⟨tr, mT, ht⟩ := paramName_trapsQS
  exact not_instantiates_of_trapsQS hready ht M inst es

/-- **`Task.startAdequacy` is false**: `paramname.wasm` satisfies its hypotheses (with the IR run
of `starts.wasm`), and the reference machine has no session run of it. -/
theorem not_startAdequacy : ¬ Task.startAdequacy := by
  intro h
  obtain ⟨m₀, inst, es, fs, m', hI, -, -, -⟩ :=
    h paramNameBytes startsComp paramNameRef startsTrace "get" [.u32 42] parse_paramName
      decodeRef_paramName paramName_valid (by decide +kernel) rfl rfl (by simp [startsTrace])
      (starts_inst _)
  exact paramName_not_instantiates m₀ inst es hI

end Silmaril.Proofs.Wasm.Component.DecoderBridge.ParamName
