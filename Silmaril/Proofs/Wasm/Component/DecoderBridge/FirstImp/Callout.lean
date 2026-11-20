module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Main
public import Silmaril.Proofs.Wasm.Component.Reference.CalloutRun

/-!
# A `canon lower` callout answered by `answerImplS`, over any engine

`Reference.CalloutRun` runs the callout program of a `canon lower` trampoline of a host function
answered by `answerImplS g` for the engines `core3P P`. The reference machine of the decoded
binaries runs the concrete engine `core3 o` (`InstRef.embL`); the callout program does not depend
on the engine, and this module restates the run for any engine `E` (the same proofs):

* `runs_calloutX`: when the flat arguments lift to `ws` and `g` answers well-typed `us` in the
  host state, moving to `s'`, the callout program runs to `.flat (lowerArgs results us)`, the
  host state becomes `s'`, and the store has one more subtask and caller record
  (`calloutSt_eqX`);
* `hostCall_lrunX`: from a core activation at such a callout, a live run of the machine to the
  activation resumed with the lowered answer.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

section Callout

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}
  {d : Call E → Canon.P E σ (Ret E)}
  {g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val →
    Option (List Silmaril.Wasm.Component.Reference.Val × σ)}

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem runsQ_allocObjX {α Id : Type} {th : Option ThreadId} (F : ArenaField E Id α) (x : α)
    {m : Machine.Config E σ}
    (hl : (ArenaOps.allocSt F x m.store).lockdown = m.store.lockdown) :
    RunsQ d th (allocObj F x) m [.tau, .tau] (F.mkId (F.size m.store))
      { m with store := ArenaOps.allocSt F x m.store } :=
  .get (.modify hl (.pure _ _))

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- The flat arguments of a callout lifted at the parameter types: `liftFlatValues` is the
IR lift, or traps. -/
theorem liftFlatValues_witFtX {cx : LiftLowerContext E} {ys : List Flat}
    {p : Silmaril.Wasm.Component.FuncTy} {ft : WIT.FuncType Empty RtId} (hmax : (ValTy.flatList p.params).length ≤ 16)
    (hps : ft.params.map (·.2) = toClosedList p.params) :
    liftFlatValues Limits.spec Quirks.none cx 16 ⟨ys, 0⟩ (ft.params.map (·.2)) =
      (ptrType cx >>= fun p' => liftFlatTypes Limits.spec Quirks.none cx p'
        (toClosedList p.params) ⟨ys, 0⟩ : Canon.P E σ _) := by
  rw [hps]
  exact liftFlatValues_toClosed (max := 16) Limits.spec Quirks.none cx hmax

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- `on_start` of a `canon_lower` caller record lifts the flat arguments. -/
theorem runs_lowerOnStartX {th : Option ThreadId} {m : Machine.Config E σ} {c : CallerId}
    {S : SubtaskId} {cx : LiftLowerContext E} {ys : List Flat}
    {p : Silmaril.Wasm.Component.FuncTy} {ft : WIT.FuncType Empty RtId} {xS : Subtask} {ws : List Silmaril.Wasm.Component.Val}
    (hc : ArenaField.callers.get? m.store c = some (.lower S cx ys 0 ft 16 1))
    (hS : ArenaField.subtasks.get? m.store S = some xS) (hidx : xS.index = none)
    (hff : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmax : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws)
    (hps : ft.params.map (·.2) = toClosedList p.params) :
    ∃ pos tr, RunsQ d th (lowerOnStart Limits.spec Quirks.none c) m tr (ws.map toRefVal)
      { m with store := LowerSt.setCallerPosSt c pos (LowerSt.startSt S m.store) } ∧
      traceObs tr = [] := by
  have hl : ∃ cur, liftFlatTypes (σ := σ) (E := E) Limits.spec Quirks.none cx
      (ptrTypeIn (LowerSt.startSt S m.store) cx) (toClosedList p.params) ⟨ys, 0⟩ =
        pure (ws.map toRefVal, cur) := by
    have h := liftFlatTypes_liftArgs (σ := σ) (E := E) Limits.spec Quirks.none cx
      (ptrTypeIn (LowerSt.startSt S m.store) cx) hff hys
    rwa [hws] at h
  obtain ⟨cur, hcur⟩ := hl
  have hmp : RunsQ d th (maybeOnProgress S) m [.tau] () m :=
    RunsQ.getObj_bind _ _ hS (by rw [hidx]; exact RunsQ.pure _ _)
  have hlf : RunsQ d th (liftFlatTypes Limits.spec Quirks.none cx
      (ptrTypeIn (LowerSt.startSt S m.store) cx) (toClosedList p.params) ⟨ys, 0⟩)
      { m with store := LowerSt.startSt S m.store } [] (ws.map toRefVal, cur)
      { m with store := LowerSt.startSt S m.store } := by
    rw [hcur]
    exact RunsQ.pure _ _
  refine ⟨cur.pos, ?_⟩
  apply Exists.intro
  refine ⟨?_, ?_⟩
  · apply RunsQ.getObj_bind _ _ hc
    apply RunsQ.bind hmp
    apply RunsQ.modify_bind _ rfl rfl
    show RunsQ _ _ (liftFlatValues Limits.spec Quirks.none cx 16 ⟨ys, 0⟩
      (ft.params.map (·.2)) >>= _) _ _ _ _
    rw [liftFlatValues_witFtX hmax hps]
    apply RunsQ.bind (RunsQ.bind (RunsQ.get (RunsQ.pure _ _)) hlf)
    exact RunsQ.modify_bind _ rfl rfl (RunsQ.pure _ _)
  · simp [traceObs, Label.obs?]

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- `on_resolve` of a `canon_lower` caller record lowers the results and resolves the
subtask. -/
theorem runs_lowerOnResolveX {th : Option ThreadId} {m : Machine.Config E σ} {c : CallerId}
    {S : SubtaskId} {cx : LiftLowerContext E} {ys : List Flat} {pos : Nat}
    {p : Silmaril.Wasm.Component.FuncTy} {ft : WIT.FuncType Empty RtId} {xS : Subtask} {us : List Silmaril.Wasm.Component.Val}
    (hc : ArenaField.callers.get? m.store c = some (.lower S cx ys pos ft 16 1))
    (hS : ArenaField.subtasks.get? m.store S = some xS) (hidx : xS.index = none)
    (_hres : p.results.length ≤ 1) (hff : floatFreeList p.results = true)
    (hus : ValTy.checkList p.results us = true) (hmax : (ValTy.flatList p.results).length ≤ 1)
    (hrs : ft.result.toList = toClosedList p.results) :
    ∃ tr, RunsQ d th (lowerOnResolve Limits.spec Quirks.none c (some (us.map toRefVal))) m tr ()
      { m with store := CStore.subtaskResolveSt S .returned (lowerArgs p.results us) m.store } ∧
      traceObs tr = [] := by
  have hmp : RunsQ d th (maybeOnProgress S) m [.tau] () m :=
    RunsQ.getObj_bind _ _ hS (by rw [hidx]; exact RunsQ.pure _ _)
  have e : lowerFlatValues Limits.spec Quirks.none cx 1 (us.map toRefVal) ft.result.toList
      (some ⟨ys, pos⟩) =
      (ptrType cx >>= fun _ => pure (lowerArgs p.results us) : Canon.P E σ _) := by
    rw [hrs]
    exact lowerFlatValues_toClosed Limits.spec Quirks.none cx hff hus hmax _
  apply Exists.intro
  refine ⟨?_, ?_⟩
  · apply RunsQ.getObj_bind _ _ hc
    apply RunsQ.bind hmp
    show RunsQ _ _ (lowerFlatValues Limits.spec Quirks.none cx 1 (us.map toRefVal)
      ft.result.toList (some ⟨ys, pos⟩) >>= _) _ _ _ _
    rw [e]
    apply RunsQ.bind (RunsQ.bind (RunsQ.get (RunsQ.pure _ _)) (RunsQ.pure _ _))
    apply RunsQ.bind (RunsQ.pure _ _)
    exact RunsQ.modify rfl (RunsQ.pure _ _)
  · simp [traceObs, Label.obs?]


/-- The `canon_lower` caller record of a callout with flat arguments `ys` to a function of type
`p`, for subtask `S` of instance `inst`. -/
def lowerRecX (S : SubtaskId) (inst : InstId) (ys : List Flat) (ft : WIT.FuncType Empty RtId)
    (pos : Nat) : Caller E :=
  .lower S { opts := {}, inst := inst, scope := .subtask S } ys pos ft 16 1

/-- The subtask of a callout of instance `inst` resolved with `flat`, before delivery. -/
def resolvedSubX (inst : InstId) (flat : List Flat) : Subtask :=
  { inst := inst, state := .returned, flatResults := flat, onCancel := CancelRef.none }

/-- The store after `canonLower` allocated the subtask and the caller record of a callout. -/
def allocSCX (s : CStore E) (inst : InstId) (ys : List Flat) (ft : WIT.FuncType Empty RtId) :
    CStore E :=
  ArenaOps.allocSt ArenaField.callers (lowerRecX  ⟨s.subtasks.length⟩ inst ys ft 0)
    (ArenaOps.allocSt ArenaField.subtasks ({ inst := inst } : Subtask) s)

/-- The store after a callout answered with the flat results `flat`. -/
def calloutStX (s : CStore E) (inst : InstId) (ys : List Flat) (ft : WIT.FuncType Empty RtId)
    (pos : Nat) (flat : List Flat) : CStore E :=
  CStore.deliverResolveSt ⟨s.subtasks.length⟩ (LowerSt.setOnCancelSt ⟨s.subtasks.length⟩ .none
    (CStore.subtaskResolveSt ⟨s.subtasks.length⟩ .returned flat
      (LowerSt.setCallerPosSt ⟨s.callers.length⟩ pos (LowerSt.startSt ⟨s.subtasks.length⟩
        (allocSCX s inst ys ft)))))

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem allocSC_callersX (s : CStore E) (inst : InstId) (ys : List Flat)
    (ft : WIT.FuncType Empty RtId) :
    ArenaField.callers.get? (allocSCX s inst ys ft) ⟨s.callers.length⟩ =
      some (lowerRecX ⟨s.subtasks.length⟩ inst ys ft 0) := by
  simp [allocSCX, ArenaOps.allocSt, ArenaField.get?, ArenaField.alloc, Arena.alloc,
    ArenaField.callers, ArenaField.subtasks, Arena.get?_eq_getElem?]

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem allocSC_subtasksX (s : CStore E) (inst : InstId) (ys : List Flat)
    (ft : WIT.FuncType Empty RtId) :
    ArenaField.subtasks.get? (allocSCX s inst ys ft) ⟨s.subtasks.length⟩ =
      some ({ inst := inst } : Subtask) := by
  simp [allocSCX, ArenaOps.allocSt, ArenaField.get?, ArenaField.alloc, Arena.alloc,
    ArenaField.callers, ArenaField.subtasks, Arena.get?_eq_getElem?]

/-- `on_start` dispatched to a `canon_lower` caller record. -/
theorem runs_onStartLowerX {th : Option ThreadId} {m m' : Machine.Config E σ} {c : CallerId}
    {x : Caller E} {tr : List (Label E σ)} {vs : List Silmaril.Wasm.Component.Reference.Val}
    (hc : ArenaField.callers.get? m.store c = some x)
    (hx : ∀ S cx ys pos ft mp mr, x = .lower S cx ys pos ft mp mr →
      RunsQ (DG (answerImplS g)) th (lowerOnStart Limits.spec Quirks.none c) m tr vs m')
    (hl : ∃ S cx ys pos ft mp mr, x = .lower S cx ys pos ft mp mr) :
    RunsQ (DG (answerImplS g)) th (DG (answerImplS g) (.onStart c)) m (.tau :: (tr ++ [])) (.vals vs) m' := by
  obtain ⟨S, cx, ys, pos, ft, mp, mr, rfl⟩ := hl
  exact RunsQ.getObj_bind _ _ hc (RunsQ.bind (hx _ _ _ _ _ _ _ rfl) (RunsQ.pure _ _))

/-- **The host function `fn` of `answerImplS g`, called through a `canon_lower` caller
record**, lifts the arguments to `ws`, and resolves with `g`'s answer `us` in the current host
state, lowered, moving to the host state `s'`. -/
theorem runs_answerX {th : Option ThreadId} {m : Machine.Config E σ} {f : FuncId}
    {ft' : WIT.FuncType Empty RtId} {fn : HostFuncId} {c : CallerId}
    {S : SubtaskId} {cx : LiftLowerContext E} {ys : List Flat}
    {p : Silmaril.Wasm.Component.FuncTy} {ft : WIT.FuncType Empty RtId} {xS : Subtask} {ws us : List Silmaril.Wasm.Component.Val}
    {s' : σ}
    (hf : ArenaField.funcs.get? m.store f = some (.host ft' fn))
    (hc : ArenaField.callers.get? m.store c = some (.lower S cx ys 0 ft 16 1))
    (hS : ArenaField.subtasks.get? m.store S = some xS) (hidx : xS.index = none)
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws)
    (hg : g m.host fn (ws.map toRefVal) = some (us.map toRefVal, s'))
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hus : ValTy.checkList p.results us = true) (hmaxr : (ValTy.flatList p.results).length ≤ 1)
    (hps : ft.params.map (·.2) = toClosedList p.params) (hrs : ft.result.toList = toClosedList p.results) :
    ∃ pos tr, RunsQ (DG (answerImplS g)) th (DG (answerImplS g) (.funcInst f c)) m tr (.cancel .none)
      { m with host := s', store := (CStore.subtaskResolveSt S .returned (lowerArgs p.results us)
        (LowerSt.setCallerPosSt c pos (LowerSt.startSt S m.store))) } ∧ traceObs tr = [] := by
  obtain ⟨pos, tr₁, h₁, hob₁⟩ := runs_lowerOnStartX (d := DG (answerImplS g)) (th := th) hc hS hidx hpf hys hmaxp hws hps
  have hc' : ArenaField.callers.get? (LowerSt.setCallerPosSt c pos (LowerSt.startSt S m.store)) c =
      some (.lower S cx ys pos ft 16 1) := by
    simp [LowerSt.setCallerPosSt, LowerSt.startSt, ArenaField.get?_modify, hc,
      LowerSt.Caller.withPos]
  have hS' : ArenaField.subtasks.get? (LowerSt.setCallerPosSt c pos (LowerSt.startSt S m.store)) S =
      some { xS with state := .started } := by
    simp [LowerSt.setCallerPosSt, LowerSt.startSt, ArenaField.get?_modify, hS]
  obtain ⟨tr₂, h₂, hob₂⟩ := runs_lowerOnResolveX (d := DG (answerImplS g)) (th := th)
    (m := { m with host := s', store := LowerSt.setCallerPosSt c pos (LowerSt.startSt S m.store) })
    hc' hS' hidx hres hrf hus hmaxr hrs
  have h₃ : RunsQ (DG (answerImplS g)) th (DG (answerImplS g) (.onResolve c (some (us.map toRefVal))))
      { m with host := s', store := LowerSt.setCallerPosSt c pos (LowerSt.startSt S m.store) }
      (.tau :: (tr₂ ++ [])) .unit
      { m with host := s', store := (CStore.subtaskResolveSt S .returned (lowerArgs p.results us)
        (LowerSt.setCallerPosSt c pos (LowerSt.startSt S m.store))) } :=
    RunsQ.getObj_bind _ _ hc' (RunsQ.bind h₂ (RunsQ.pure _ _))
  refine ⟨pos, ?_⟩
  apply Exists.intro
  refine ⟨?_, ?_⟩
  · apply RunsQ.getObj_bind _ _ hf
    apply RunsQ.call_bind (runs_onStartLowerX hc (fun _ _ _ _ _ _ _ _ => h₁) ⟨_, _, _, _, _, _, _, rfl⟩)
    apply RunsQ.hostGet
    show RunsQ _ _ (match g m.host fn (ws.map toRefVal) with
      | some (rs, s') => _
      | none => trap (TrapReason.hostTrap "answerImpl: no answer")) _ _ _ _
    rw [hg]
    exact RunsQ.hostSet (RunsQ.bind (RunsQ.pure _ _)
      (RunsQ.bind (RunsQ.call_bind h₃ (RunsQ.pure _ _)) (RunsQ.pure _ _)))
  · simp only [traceObs] at hob₁ hob₂ ⊢
    simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Label.obs?, hob₁,
      hob₂, List.nil_append, List.append_nil]

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- The end of a synchronous `canonLower` whose subtask has resolved: the resolution is
delivered and the flat results returned. -/
theorem runs_lowerTailX {th : Option ThreadId} {m : Machine.Config E σ} {S : SubtaskId}
    {X : Subtask} (hS : ArenaField.subtasks.get? m.store S = some X) (hst : X.state = .returned)
    (hlen : X.lenders = some []) :
    RunsQ d th (do
        let resolved ← gets fun x => x.subtaskResolved S
        (if (!resolved) = true then Thread.waitUntilGuest WaitSite.syncLower (ReadyCond.subtaskResolved S)
          else pure () : Canon.P E σ Unit)
        Subtask.deliverResolve S
        let y ← getObj ArenaField.subtasks S
        pure y.flatResults) m [.tau, .tau, .tau] X.flatResults
      { m with store := CStore.deliverResolveSt S m.store } := by
  have hr : m.store.subtaskResolved S = true := by
    simp only [CStore.subtaskResolved, CStore.subtask?, hS, hst]
    rfl
  have hd : CStore.deliverResolveSt S m.store =
      ArenaField.subtasks.modify m.store S fun y => { y with lenders := none } := by
    simp only [CStore.deliverResolveSt, CStore.subtask?, hS, hlen, Option.getD_some, List.foldl_nil]
  have hS' : ArenaField.subtasks.get? (CStore.deliverResolveSt S m.store) S =
      some { X with lenders := none } := by
    rw [hd, ArenaField.get?_modify_self, hS]
    rfl
  apply RunsQ.get
  show RunsQ _ _ ((if (!m.store.subtaskResolved S) = true then
    Thread.waitUntilGuest WaitSite.syncLower (ReadyCond.subtaskResolved S) else pure ()) >>= _) _ _ _ _
  rw [hr]
  apply RunsQ.bind (RunsQ.pure _ _)
  apply RunsQ.modify (by rw [hd]; rfl)
  exact RunsQ.getObj_bind _ _ hS' (RunsQ.pure _ _)

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- The resolved subtask of a callout. -/
theorem subtasks_resolvedX (s : CStore E) (inst : InstId) (ys : List Flat)
    (ft : WIT.FuncType Empty RtId) (pos : Nat) (flat : List Flat) :
    ArenaField.subtasks.get? (LowerSt.setOnCancelSt ⟨s.subtasks.length⟩ CancelRef.none
      (CStore.subtaskResolveSt ⟨s.subtasks.length⟩ .returned flat
        (LowerSt.setCallerPosSt ⟨s.callers.length⟩ pos (LowerSt.startSt ⟨s.subtasks.length⟩
          (allocSCX s inst ys ft))))) ⟨s.subtasks.length⟩ =
      some (resolvedSubX inst flat) := by
  simp [LowerSt.setOnCancelSt, CStore.subtaskResolveSt, LowerSt.setCallerPosSt, LowerSt.startSt,
    ArenaField.get?_modify, allocSC_subtasksX, resolvedSubX]

/-- **`canonLower` of a callout answered by `g`.** -/
theorem runs_canonLowerX {th : Option ThreadId} {m : Machine.Config E σ} {f : FuncId}
    {ft' : WIT.FuncType Empty RtId} {fn : HostFuncId} {inst : InstId} {st : InstState}
    {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy} {ft : WIT.FuncType Empty RtId} {ws us : List Silmaril.Wasm.Component.Val}
    {s' : σ}
    (hi : ArenaField.insts.get? m.store inst = some st) (hleave : st.mayLeave = true)
    (hf : ArenaField.funcs.get? m.store f = some (.host ft' fn))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws)
    (hg : g m.host fn (ws.map toRefVal) = some (us.map toRefVal, s'))
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hus : ValTy.checkList p.results us = true) (hmaxr : (ValTy.flatList p.results).length ≤ 1)
    (hps : ft.params.map (·.2) = toClosedList p.params) (hrs : ft.result.toList = toClosedList p.results) :
    ∃ pos tr, RunsQ (DG (answerImplS g)) th (canonLower Limits.spec Quirks.none f ft {} inst ys) m tr
      (lowerArgs p.results us)
      { m with host := s', store := calloutStX m.store inst ys ft pos (lowerArgs p.results us) } ∧
      traceObs tr = [] := by
  obtain ⟨pos, tr₁, h₁, hob₁⟩ := runs_answerX (g := g) (th := th)
    (m := { m with store := allocSCX m.store inst ys ft }) hf (allocSC_callersX _ _ _ _)
    (allocSC_subtasksX _ _ _ _) rfl hpf hys hmaxp hws hg hres hrf hus hmaxr hps hrs
  have ht := runs_lowerTailX (d := DG (answerImplS g)) (th := th) (m := { m with host := s', store :=
    (LowerSt.setOnCancelSt ⟨m.store.subtasks.length⟩ CancelRef.none
      (CStore.subtaskResolveSt ⟨m.store.subtasks.length⟩ .returned (lowerArgs p.results us)
        (LowerSt.setCallerPosSt ⟨m.store.callers.length⟩ pos
          (LowerSt.startSt ⟨m.store.subtasks.length⟩ (allocSCX m.store inst ys ft))))) })
    (subtasks_resolvedX _ _ _ _ _ _) rfl rfl
  refine ⟨pos, ?_⟩
  apply Exists.intro
  refine ⟨?_, ?_⟩
  · apply RunsQ.getObj_bind _ _ hi
    rw [hleave]
    apply RunsQ.bind (RunsQ.pure _ _)
    apply RunsQ.bind (runsQ_allocObjX _ _ rfl)
    apply RunsQ.bind (runsQ_allocObjX _ _ rfl)
    apply RunsQ.call_bind h₁
    apply RunsQ.modify rfl
    exact ht
  · simp only [traceObs] at hob₁ ⊢
    simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Label.obs?, hob₁,
      List.nil_append, List.append_nil]

/-- The prefix of the callout program: the entry check passes. -/
theorem runs_hostCallout_ofX {th : Option ThreadId} {m m' : Machine.Config E σ}
    {f : FuncId} {inst : InstId} {ys : List Flat} {ft : WIT.FuncType Empty RtId}
    {tr : List (Label E σ)} {flat : List Flat}
    (hentry : calloutEntry m.store th (.lowered f ft {} inst) = none)
    (h : RunsQ (DG (answerImplS g)) th (canonLower Limits.spec Quirks.none f ft {} inst ys) m tr flat m') :
    RunsQ (DG (answerImplS g)) th (DG (answerImplS g) (.hostCallout (.lowered f ft {} inst) ys)) m
      (.tau :: .tau :: (tr ++ [])) (.flat flat) m' := by
  apply RunsQ.currentThread
  apply RunsQ.get
  show RunsQ _ _ (match calloutEntry m.store th (.lowered f ft {} inst) with
    | some r => trap r | none => _) _ _ _ _
  rw [hentry]
  exact RunsQ.bind h (RunsQ.pure _ _)

/-- **A callout answered by `g`** runs deterministically to its flat results. -/
theorem runs_calloutX {th : Option ThreadId} {m : Machine.Config E σ} {f : FuncId}
    {ft' : WIT.FuncType Empty RtId} {fn : HostFuncId} {inst : InstId} {st : InstState}
    {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy} {ft : WIT.FuncType Empty RtId} {ws us : List Silmaril.Wasm.Component.Val}
    (hentry : calloutEntry m.store th (.lowered f ft {} inst) = none)
    (hi : ArenaField.insts.get? m.store inst = some st) (hleave : st.mayLeave = true)
    (hf : ArenaField.funcs.get? m.store f = some (.host ft' fn))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws)
    {s' : σ} (hg : g m.host fn (ws.map toRefVal) = some (us.map toRefVal, s'))
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hus : ValTy.checkList p.results us = true) (hmaxr : (ValTy.flatList p.results).length ≤ 1)
    (hps : ft.params.map (·.2) = toClosedList p.params) (hrs : ft.result.toList = toClosedList p.results) :
    ∃ pos tr, RunsQ (DG (answerImplS g)) th (DG (answerImplS g) (.hostCallout (.lowered f ft {} inst) ys)) m tr
      (.flat (lowerArgs p.results us))
      { m with host := s', store := calloutStX m.store inst ys ft pos (lowerArgs p.results us) } ∧
      traceObs tr = [] := by
  obtain ⟨pos, tr, h, hob⟩ := runs_canonLowerX (g := g) (th := th) hi hleave hf hpf hys hmaxp hws hg hres
    hrf hus hmaxr hps hrs
  exact ⟨pos, _, runs_hostCallout_ofX hentry h, by
    simp only [traceObs] at hob ⊢
    simp only [List.filterMap_cons, Label.obs?, hob, List.append_nil]⟩

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- **The store after a callout** has one more subtask and one more caller record. -/
theorem calloutSt_eqX (s : CStore E) (inst : InstId) (ys : List Flat)
    (ft : WIT.FuncType Empty RtId) (pos : Nat) (flat : List Flat) :
    calloutStX s inst ys ft pos flat =
      { s with
          subtasks := s.subtasks ++ [{ resolvedSubX inst flat with lenders := none }]
          callers := s.callers ++ [lowerRecX ⟨s.subtasks.length⟩ inst ys ft pos] } := by
  have hd := subtasks_resolvedX s inst ys ft pos flat
  simp only [calloutStX, CStore.deliverResolveSt, CStore.subtask?, hd]
  simp [allocSCX, ArenaOps.allocSt, ArenaField.alloc, Arena.alloc, ArenaField.modify, Arena.modify,
    ArenaField.subtasks, ArenaField.callers, LowerSt.setOnCancelSt, CStore.subtaskResolveSt,
    LowerSt.setCallerPosSt, LowerSt.startSt, modify_concat_length, resolvedSubX, lowerRecX,
    LowerSt.Caller.withPos]


end Callout

/-! ## The callout as a machine run -/

section Machine

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type} {prof : ProfileKind}
  {g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val →
    Option (List Silmaril.Wasm.Component.Reference.Val × σ)}
  {B : Machine.Config E σ} {th : Option ThreadId}
  {K : List Flat → Canon.P E σ (Ret E)} {segs : List (Seg E σ)}
  {rest : List (Activation E σ)} {y : CoreSt E} {f : FuncId}
  {ft' : WIT.FuncType Empty RtId} {fn : HostFuncId} {inst : InstId} {st : InstState}
  {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy} {ft : WIT.FuncType Empty RtId}

/-- **An answered host call, as a live run**: from the core activation at the callout to the
core activation resumed with the lowered answer, the host state moved to `s'`, one more
subtask and one more `canon_lower` caller record in the store. -/
theorem hostCall_lrunX (hl : B.store.lockdown = false)
    (hst : E.status y.1 y.2 = .callout (.lowered f ft {} inst) ys)
    (hentry : calloutEntry B.store th (.lowered f ft {} inst) = none)
    (hi : ArenaField.insts.get? B.store inst = some st) (hleave : st.mayLeave = true)
    (hf : ArenaField.funcs.get? B.store f = some (.host ft' fn))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) {ws : List Silmaril.Wasm.Component.Val}
    (hws : liftArgs p.params ys = some ws) {us : List Silmaril.Wasm.Component.Val} {s' : σ}
    (hg : g B.host fn (ws.map toRefVal) = some (us.map toRefVal, s'))
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hus : ValTy.checkList p.results us = true) (hmaxr : (ValTy.flatList p.results).length ≤ 1)
    (hps : ft.params.map (·.2) = toClosedList p.params) (hrs : ft.result.toList = toClosedList p.results) :
    ∃ (pos : Nat) (tr : List (Label E σ)),
      LRun prof (fun _ _ => false) (DG (answerImplS g)) (coreCfg B th K segs rest y) (.tau :: tr)
        (coreCfg { B with host := s', store := { B.store with
            subtasks := B.store.subtasks ++
              [{ resolvedSubX inst (lowerArgs p.results us) with lenders := none }]
            callers := B.store.callers ++ [lowerRecX ⟨B.store.subtasks.length⟩ inst ys ft pos] } }
          th K segs rest (y.1, E.resume y.1 y.2 (.values (lowerArgs p.results us)))) ∧
        traceObs tr = [] := by
  obtain ⟨pos, tr, h, hob⟩ := runs_calloutX (g := g) (th := th) (m := coreCfg B th K segs rest y)
    hentry hi hleave hf hpf hys hmaxp hws hg hres hrf hus hmaxr hps hrs
  have hl' : (coreCfg B th K segs rest y).store.lockdown = false := hl
  have d₁ := h.lrun (prof := prof) (hr := fun _ _ => false) hl' Prog.pure (.core y.2 K :: segs)
    rest
  rw [Prog.bind_eq, Prog.bind_pure, calloutSt_eqX] at d₁
  have hne : E.status y.1 y.2 ≠ .running ∧ E.status y.1 y.2 ≠ .stuck := by
    rw [hst]
    exact ⟨(fun e => by cases e), (fun e => by cases e)⟩
  have s₀ : UniqueStep prof (fun _ _ => false) (DG (answerImplS g))
      (coreCfg B th K segs rest y) .tau
      { coreCfg B th K segs rest y with ctl := ⟨th, .prog (DG (answerImplS g)
        (.hostCallout (.lowered f ft {} inst) ys)), .core y.2 K :: segs⟩ :: rest } :=
    UniqueStep.of_core rfl hne (Step.coreCallout rfl hst)
  have hlive : Live ({ coreCfg B th K segs rest y with
      host := s', store := { (coreCfg B th K segs rest y).store with
        subtasks := (coreCfg B th K segs rest y).store.subtasks ++
          [{ resolvedSubX inst (lowerArgs p.results us) with lenders := none }]
        callers := (coreCfg B th K segs rest y).store.callers ++
          [lowerRecX ⟨(coreCfg B th K segs rest y).store.subtasks.length⟩ inst ys ft pos] },
      ctl := ⟨th, .prog (Prog.pure (.flat (lowerArgs p.results us))), .core y.2 K :: segs⟩ ::
        rest } : Machine.Config E σ) :=
    ⟨List.cons_ne_nil _ _, hl⟩
  exact ⟨pos, _ ++ [.tau], .cons ⟨List.cons_ne_nil _ _, hl⟩ s₀ (d₁.trans (.cons hlive
    (.of_prog rfl (fun _ _ e => by cases e) (Step.popCore rfl)) (.refl _))), by
    simp only [traceObs] at hob ⊢
    simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Label.obs?, hob,
      List.append_nil]⟩

end Machine

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
