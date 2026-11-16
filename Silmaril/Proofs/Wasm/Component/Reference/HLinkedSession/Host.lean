module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Stat
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Silent
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.TrapH

/-!
# Forward runs of a call of `HLinked2.toRef`: a host call

The importer's core activation of an `HLinked2` stopped at the callout of a host import (the
`canon lower` trampoline of host function `fn`), under the stateful host `answerHostS P g`
(dispatcher `DI P (answerImplS g)`), from any configuration `coreCfg B th K segs rest y`:

* `hostCall_fwd`: when the arguments lift to `ws` and `g` answers well-typed `us` in the host
  state, moving to `s'`, the machine runs (quietly) the callout step, the callout program
  (`runs_callout`: `canonLower`, the host function, the delivery) and the `popCore` step, to the
  core activation resumed with `lowerArgs p.results us`, the host state `s'` and one more subtask
  and caller record in the store (the core store is unchanged);
* `hostCall_noAnswer`, `hostCall_noLift`: when `g` has no answer (`hostTrap`), or the arguments
  do not lift (a lift trap), the machine traps with a specification trap (`TrapEnd`) at the
  core store of the callout; `hostCall_noAnswerH`, `hostCall_noLiftG` add the host state of the
  trapped configuration (`TrapEndH`, that of the frame), the latter for every host whose
  functions start with `on_start` (`answerImplS g`, `HLinked2.silentImpl`);
* `LInv.resumeHost_fwdH`: on the importer's side, the part resumed with the lowered answer and
  the shared thread resumed with it satisfy `LInv` again, with the same exporter store.

**A host answer that is not well typed is not a trap.** `answerImplS` resolves the subtask with
whatever `g` answers, and `lowerOnResolve` lowers it at the import's result types; on a
shape mismatch this is the `internal` fault `"lower_flat: value does not match type"`, which
`Calls` does not accept as a trap outcome. Counterexample: a host import `h : func() -> u32`
whose host answers `[]` (the IR value list `[]`, so `HostAnswersS` holds with
`R = some (.vals [])`): the specification lowers nothing (`checkLower [u32] [] = none`) and the
importer traps, while the reference machine runs `lowerFlatTypes [] [u32] = flatMismatch`. The
forward host segment therefore assumes a well-typed answer (`hus`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Rel4 Grow Touch)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

variable {P : Profile} {σ : Type} {prof : ProfileKind}
  {g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val →
    Option (List Silmaril.Wasm.Component.Reference.Val × σ)}

/-! ## The machine -/

section Machine

variable {B : Machine.Config (E3 P) σ} {th : Option ThreadId}
  {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
  {rest : List (Activation (E3 P) σ)} {y : CoreSt (E3 P)} {f : FuncId}
  {ft' : WIT.FuncType Empty RtId} {fn : HostFuncId} {inst : InstId} {st : InstState}
  {ys : List Flat} {p : FuncTy}

/-- **An answered host call, forward**: from the core activation at the callout to the core
activation resumed with the lowered answer, quietly, the host state moved to `s'`, one more
subtask (resolved, delivered) and one more `canon_lower` caller record in the store. -/
theorem hostCall_fwd (hl : B.store.lockdown = false)
    (hst : (E3 P).status y.1 y.2 = .callout (.lowered f (witFt p) {} inst) ys)
    (hentry : calloutEntry B.store th (.lowered f (witFt p) {} inst) = none)
    (hi : ArenaField.insts.get? B.store inst = some st) (hleave : st.mayLeave = true)
    (hf : ArenaField.funcs.get? B.store f = some (.host ft' fn))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) {ws : List Silmaril.Wasm.Component.Val}
    (hws : liftArgs p.params ys = some ws) {us : List Silmaril.Wasm.Component.Val} {s' : σ}
    (hg : g B.host fn (ws.map toRefVal) = some (us.map toRefVal, s'))
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hus : ValTy.checkList p.results us = true) (hmaxr : (ValTy.flatList p.results).length ≤ 1) :
    ∃ (pos : Nat) (tr : List (Label (E3 P) σ)), Quiet tr ∧
      Steps prof (fun _ _ => false) (DI P (answerImplS g)) (coreCfg B th K segs rest y) tr
        (coreCfg { B with host := s', store := { B.store with
            subtasks := B.store.subtasks ++
              [{ resolvedSub inst (lowerArgs p.results us) with lenders := none }]
            callers := B.store.callers ++ [lowerRec ⟨B.store.subtasks.length⟩ inst ys p pos] } }
          th K segs rest (y.1, (E3 P).resume y.1 y.2 (.values (lowerArgs p.results us)))) := by
  obtain ⟨pos, tr, h⟩ := runs_callout (g := g) (th := th) (m := coreCfg B th K segs rest y)
    hentry hi hleave hf hpf hys hmaxp hws hg hres hrf hus hmaxr
  have hl' : (coreCfg B th K segs rest y).store.lockdown = false := hl
  have d₁ := h.lrun (prof := prof) (hr := fun _ _ => false) hl' Prog.pure (.core y.2 K :: segs)
    rest
  rw [Prog.bind_eq, Prog.bind_pure, calloutSt_eq] at d₁
  have s₀ : Step prof (fun _ _ => false) (DI P (answerImplS g)) (coreCfg B th K segs rest y) .tau
      { coreCfg B th K segs rest y with ctl := ⟨th, .prog (DI P (answerImplS g)
        (.hostCallout (.lowered f (witFt p) {} inst) ys)), .core y.2 K :: segs⟩ :: rest } :=
    Step.coreCallout rfl hst
  have hlive : Live ({ coreCfg B th K segs rest y with
      host := s', store := { (coreCfg B th K segs rest y).store with
        subtasks := (coreCfg B th K segs rest y).store.subtasks ++
          [{ resolvedSub inst (lowerArgs p.results us) with lenders := none }]
        callers := (coreCfg B th K segs rest y).store.callers ++
          [lowerRec ⟨(coreCfg B th K segs rest y).store.subtasks.length⟩ inst ys p pos] },
      ctl := ⟨th, .prog (Prog.pure (.flat (lowerArgs p.results us))), .core y.2 K :: segs⟩ ::
        rest } : Machine.Config (E3 P) σ) :=
    ⟨List.cons_ne_nil _ _, hl⟩
  refine ⟨pos, .tau :: (_ ++ [.tau]), Quiet.tau.append ((Quiet.of_lrun d₁ hlive).append
    Quiet.tau), .cons s₀ (Adequacy.steps_append d₁.steps (.cons (Step.popCore rfl) (.refl _)))⟩

/-- A configuration whose focus is the callout program, as `p >>= pure`. -/
theorem ctl_bind_pure {M : Machine.Config (E3 P) σ} {q : Canon.P (E3 P) σ (Ret (E3 P))}
    (hc : M.ctl = ⟨th, .prog q, segs⟩ :: rest) : M.ctl = ⟨th, .prog (q >>= Prog.pure), segs⟩ :: rest := by
  rw [Prog.bind_eq, Prog.bind_pure]
  exact hc

/-- **A host call that the host does not answer traps** (`hostTrap`), at the core store of
the callout and the host state of the frame. -/
theorem hostCall_noAnswerH (hl : B.store.lockdown = false)
    (hst : (E3 P).status y.1 y.2 = .callout (.lowered f (witFt p) {} inst) ys)
    (hentry : calloutEntry B.store th (.lowered f (witFt p) {} inst) = none)
    (hi : ArenaField.insts.get? B.store inst = some st) (hleave : st.mayLeave = true)
    (hf : ArenaField.funcs.get? B.store f = some (.host ft' fn))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) {ws : List Silmaril.Wasm.Component.Val}
    (hws : liftArgs p.params ys = some ws) (hg : g B.host fn (ws.map toRefVal) = none) :
    TrapEndH prof P (answerImplS g) (coreCfg B th K segs rest y) y.1 B.host := by
  let m : Machine.Config (E3 P) σ := coreCfg B th K segs rest y
  let C : CallerId := ⟨m.store.callers.length⟩
  let m₂ : Machine.Config (E3 P) σ := { m with store := allocSC m.store inst ys p }
  obtain ⟨pos, tr₁, h₁⟩ := runs_lowerOnStart (d := DI P (answerImplS g)) (th := th) (m := m₂)
    (allocSC_callers _ _ _ _) (allocSC_subtasks _ _ _ _) rfl hpf hys hmaxp hws
  have hon := runs_onStartLowerI (impl := answerImplS g) (allocSC_callers m.store inst ys p)
    (fun _ _ _ _ _ _ _ _ => h₁) ⟨_, _, _, _, _, _, _, rfl⟩
  have hfn : ∃ tr, TrapsQS (DI P (answerImplS g)) th
      ((answerImplS g : HostImpl (E3 P) σ).funcs fn C) m₂ tr
      { m₂ with store :=
        (LowerSt.setCallerPosSt C pos (LowerSt.startSt ⟨m.store.subtasks.length⟩ m₂.store)) } := by
    apply Exists.intro
    apply TrapsQS.bind (RunsQ.call_bind hon (RunsQ.pure _ _))
    apply TrapsQS.bind (RunsQ.hostGet (RunsQ.pure _ _))
    show TrapsQS _ _ (match g B.host fn (ws.map toRefVal) with
      | some (rs, s') => _
      | none => trap (TrapReason.hostTrap "answerImpl: no answer")) _ _ _
    rw [hg]
    exact TrapsQS.trap _ ⟨_, _, (fun _ h => by cases h), rfl⟩
  have hf₂ : ArenaField.funcs.get? (allocSC m.store inst ys p) f = some (.host ft' fn) := hf
  have hcl : ∃ tr, TrapsQS (DI P (answerImplS g)) th
      (DI P (answerImplS g) (.hostCallout (.lowered f (witFt p) {} inst) ys)) m tr
      { m₂ with store :=
        (LowerSt.setCallerPosSt C pos (LowerSt.startSt ⟨m.store.subtasks.length⟩ m₂.store)) } := by
    apply Exists.intro
    apply TrapsQS.bind (RunsQ.currentThread (RunsQ.pure _ _))
    apply TrapsQS.bind (RunsQ.get (RunsQ.pure _ _))
    show TrapsQS _ _ (match calloutEntry m.store th (.lowered f (witFt p) {} inst) with
      | some r => trap r | none => _) _ _ _
    rw [show calloutEntry m.store th (.lowered f (witFt p) {} inst) = none from hentry]
    apply TrapsQS.left
    apply TrapsQS.bind (runs_getObj ArenaField.insts inst m hi)
    rw [hleave]
    apply TrapsQS.bind (RunsQ.pure _ _)
    apply TrapsQS.bind (runsQ_allocObj _ _ rfl)
    apply TrapsQS.bind (runsQ_allocObj _ _ rfl)
    apply TrapsQS.left
    apply TrapsQS.callIn
    exact TrapsQS.bind (RunsQ.getObj _ _ hf₂) hfn.choose_spec
  obtain ⟨tr, h⟩ := hcl
  have s₀ : Step prof (fun _ _ => false) (DI P (answerImplS g)) m .tau
      { m with ctl := ⟨th, .prog (DI P (answerImplS g)
        (.hostCallout (.lowered f (witFt p) {} inst) ys)), .core y.2 K :: segs⟩ :: rest } :=
    Step.coreCallout rfl hst
  refine TrapEndH.steps (.cons s₀ (.refl _)) Quiet.tau
    (TrapsAtSH.trapEndH (TrapsQS.trapsAtSH (ctl_bind_pure rfl) (h.withCtl _) hl ?_ ?_)) <;> rfl

/-- **A host call that the host does not answer traps** (`hostTrap`), at the core store of
the callout. -/
theorem hostCall_noAnswer (hl : B.store.lockdown = false)
    (hst : (E3 P).status y.1 y.2 = .callout (.lowered f (witFt p) {} inst) ys)
    (hentry : calloutEntry B.store th (.lowered f (witFt p) {} inst) = none)
    (hi : ArenaField.insts.get? B.store inst = some st) (hleave : st.mayLeave = true)
    (hf : ArenaField.funcs.get? B.store f = some (.host ft' fn))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) {ws : List Silmaril.Wasm.Component.Val}
    (hws : liftArgs p.params ys = some ws) (hg : g B.host fn (ws.map toRefVal) = none) :
    TrapEnd prof P (answerImplS g) (coreCfg B th K segs rest y) y.1 :=
  (hostCall_noAnswerH hl hst hentry hi hleave hf hpf hys hmaxp hws hg).toEnd

/-- **A host call whose arguments do not lift traps** (a lift trap), at the core store of the
callout and the host state of the frame, for every host whose function `fn` starts with
`on_start`. -/
theorem hostCall_noLiftG {impl : HostImpl (E3 P) σ}
    (himpl : ∀ C, ∃ k : List Silmaril.Wasm.Component.Reference.Val → Canon.P (E3 P) σ (Ret (E3 P)),
      impl.funcs fn C = callVals (.onStart C) >>= k) (hl : B.store.lockdown = false)
    (hst : (E3 P).status y.1 y.2 = .callout (.lowered f (witFt p) {} inst) ys)
    (hentry : calloutEntry B.store th (.lowered f (witFt p) {} inst) = none)
    (hi : ArenaField.insts.get? B.store inst = some st) (hleave : st.mayLeave = true)
    (hf : ArenaField.funcs.get? B.store f = some (.host ft' fn))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none) :
    TrapEndH prof P impl (coreCfg B th K segs rest y) y.1 B.host := by
  let m : Machine.Config (E3 P) σ := coreCfg B th K segs rest y
  let C : CallerId := ⟨m.store.callers.length⟩
  let m₂ : Machine.Config (E3 P) σ := { m with store := allocSC m.store inst ys p }
  obtain ⟨tr₁, h₁⟩ := traps_lowerOnStartS (impl := impl) (th := th) (m := m₂)
    (allocSC_callers _ _ _ _) (allocSC_subtasks _ _ _ _) rfl hpf hys hmaxp hws
  have hfn : TrapsQS (DI P impl) th
      ((impl : HostImpl (E3 P) σ).funcs fn C) m₂ (.tau :: (.tau :: tr₁))
      { m₂ with store := LowerSt.startSt ⟨m.store.subtasks.length⟩ m₂.store } := by
    obtain ⟨kf, hkf⟩ := himpl C
    rw [hkf]
    exact TrapsQS.left (TrapsQS.callIn (TrapsQS.bind (RunsQ.getObj _ _ (allocSC_callers _ _ _ _))
      (TrapsQS.left h₁)))
  have hf₂ : ArenaField.funcs.get? (allocSC m.store inst ys p) f = some (.host ft' fn) := hf
  have hcl : ∃ tr, TrapsQS (DI P impl) th
      (DI P impl (.hostCallout (.lowered f (witFt p) {} inst) ys)) m tr
      { m₂ with store := LowerSt.startSt ⟨m.store.subtasks.length⟩ m₂.store } := by
    apply Exists.intro
    apply TrapsQS.bind (RunsQ.currentThread (RunsQ.pure _ _))
    apply TrapsQS.bind (RunsQ.get (RunsQ.pure _ _))
    show TrapsQS _ _ (match calloutEntry m.store th (.lowered f (witFt p) {} inst) with
      | some r => trap r | none => _) _ _ _
    rw [show calloutEntry m.store th (.lowered f (witFt p) {} inst) = none from hentry]
    apply TrapsQS.left
    apply TrapsQS.bind (runs_getObj ArenaField.insts inst m hi)
    rw [hleave]
    apply TrapsQS.bind (RunsQ.pure _ _)
    apply TrapsQS.bind (runsQ_allocObj _ _ rfl)
    apply TrapsQS.bind (runsQ_allocObj _ _ rfl)
    apply TrapsQS.left
    apply TrapsQS.callIn
    exact TrapsQS.bind (RunsQ.getObj _ _ hf₂) hfn
  obtain ⟨tr, h⟩ := hcl
  have s₀ : Step prof (fun _ _ => false) (DI P impl) m .tau
      { m with ctl := ⟨th, .prog (DI P impl
        (.hostCallout (.lowered f (witFt p) {} inst) ys)), .core y.2 K :: segs⟩ :: rest } :=
    Step.coreCallout rfl hst
  refine TrapEndH.steps (.cons s₀ (.refl _)) Quiet.tau
    (TrapsAtSH.trapEndH (TrapsQS.trapsAtSH (ctl_bind_pure rfl) (h.withCtl _) hl ?_ ?_)) <;> rfl

/-- **A host call whose arguments do not lift traps** (a lift trap), at the core store of the
callout. -/
theorem hostCall_noLift (hl : B.store.lockdown = false)
    (hst : (E3 P).status y.1 y.2 = .callout (.lowered f (witFt p) {} inst) ys)
    (hentry : calloutEntry B.store th (.lowered f (witFt p) {} inst) = none)
    (hi : ArenaField.insts.get? B.store inst = some st) (hleave : st.mayLeave = true)
    (hf : ArenaField.funcs.get? B.store f = some (.host ft' fn))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none) :
    TrapEnd prof P (answerImplS g) (coreCfg B th K segs rest y) y.1 :=
  (hostCall_noLiftG (fun _ => ⟨_, rfl⟩) hl hst hentry hi hleave hf hpf hys hmaxp hws).toEnd

end Machine

/-! ## The importer's side -/

section Inv

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B : Machine.Config (E3 P) σ} {Op₀ Oc₀ : Own}
  {f : Ii.F.Op}

/-- **After an answered host call the invariant holds again**: the shared thread resumed with
the lowering of the answer `us` and the part resumed with the same values satisfy `LInv` at the
same core store and exporter store. -/
theorem LInv.resumeHost_fwdH (S : HStat P l Ie Ii u₀ F₀ B Op₀) {y : CoreSt (E3 P)}
    {x : Store Nat × STh} {π : Store Nat} (hI : LInv P l.toW Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π)
    {k : Nat} {nm : String} {p : FuncTy} {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val} {e : Ii.E.Op}
    (hk : l.imp.imports[k]? = some (nm, p))
    (hdx : Silmaril.Wasm.SingleThreaded.decompose? x.1 (x.2.config x.1).code = some (E, a, k, args))
    (he : Ii.importOp? k args = some e) {us : List Silmaril.Wasm.Component.Val}
    (hus : ValTy.checkList p.results us = true) :
    LInv P l.toW Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f
      (y.1, (E3 P).resume y.1 y.2 (.values (lowerArgs p.results us)))
      (x.1, Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2
        (.values ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))) π := by
  obtain ⟨ρp, Op, ρc, Oc, hL, hR⟩ := hI.rel
  have hL2 : LinkSt s₀ ρc Oc
      (x.1, Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2
        (.values ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)))
      (Store.mapH (gL P l.toW) y.1, Silmaril.Wasm.SingleThreaded.resumeResult
        (Store.mapH (gL P l.toW) y.1) y.2
        (.values ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))) :=
    link_resume hL hdx (ofFlat_scalar _)
  have hres : (E3 P).resume y.1 y.2 (.values (lowerArgs p.results us)) =
      Silmaril.Wasm.SingleThreaded.resumeResult (Store.mapH (gL P l.toW) y.1) y.2
        (.values ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)) :=
    (resume_values y.1 y.2 _).trans (resumeResult_mapH (gL P l.toW) y.1 y.2 _).symm
  have hek : e.1.val = k ∧ e.2.1 = args := ifaceOp?_some he
  have hdx' : Silmaril.Wasm.SingleThreaded.decompose? (x.2.config x.1).store
      (x.2.config x.1).code = some (E, a, k, args) :=
    (Silmaril.Wasm.SingleThreaded.Thread.config_store x.1 x.2).symm ▸ hdx
  have hstep : Silmaril.Wasm.Game.SStep P (valEnv Ii) (x.2.config x.1, ())
      (⟨(x.2.config x.1).store, (x.2.config x.1).frame,
        E.fill (Silmaril.Wasm.Execution.Core.Result.values
          ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)).toAdmin⟩, ()) :=
    Silmaril.Wasm.Game.SStep.answer (P := P) (L := valEnv Ii) (q := ()) (q' := ())
      (w := .values ⟨_, resAnswerH S hk hek.1 hus⟩) hdx' he ⟨_, rfl⟩
  have hcfg := resumeResult_config hdx'
    (.values ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))
  refine ⟨⟨ρp, Op, ρc, Oc, hres ▸ hL2, hR⟩, hI.fnE, hI.wf, hI.funcs, ?_⟩
  show Silmaril.Wasm.Game.SSteps P (valEnv Ii) _ (Silmaril.Wasm.SingleThreaded.Thread.config x.1
    (Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2 _), ())
  rw [hcfg]
  exact hI.run.tail hstep

end Inv

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
