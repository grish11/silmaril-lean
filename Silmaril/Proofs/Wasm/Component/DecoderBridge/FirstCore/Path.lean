module

public import Silmaril.Proofs.Wasm.Component.Reference.StartCall

/-!
# The start call during instantiation, over any engine and host state

`Proofs.Wasm.Component.Reference.StartCall.start_at` runs `Instantiate.runStart ⟨0⟩ a` to the
core activation of the start function, over `core3P P` with host state `Unit` and the
reference host. The reference machine of the decoded test binaries is over `core3 neverFail`
with the logging host (`InstRef.embL`, host state `Unit × log`). The path to the core
activation reads neither the engine's internal step nor its status, nor the host state; this
file restates it for every engine `E`, host state `σ` and host functions `impl` (the
specification dispatcher `DG impl`):

* the store lemmas of `MultiBase` (`tasks_get_lastG`, `threadStatus_lastG`, `enter_eqG`, …)
  and the program runs of `MultiProgs`/`CallPath`/`StartCall` (`runs_enterG`, `runs_startSG`,
  …), with the same proofs over any `E`;
* `start_coreG`: from the instantiation program at `runStart ⟨0⟩ a`, a live run (no host event,
  no trap, no observation) to the core activation `E.invoke a []`, with the core store and the
  lockdown flag unchanged.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs

variable {E : CoreEngine} {σ : Type}

/-- The specification dispatcher with no ready host waitables and the host functions `impl`
(`Reference.DI` over any engine). -/
abbrev DG [∀ a b, Decidable (E.ExternSub a b)] (impl : HostImpl E σ) : Call E → Canon.P E σ (Ret E) :=
  Canon.dispatch Limits.spec Quirks.none (fun _ _ => false) impl

/-! ## Arenas -/

theorem tasks_get_lastG {s : CStore E} {Gt : List (Runtime.Task E)} {y : Runtime.Task E}
    (h : s.tasks = Gt ++ [y]) : ArenaField.tasks.get? s (⟨Gt.length⟩ : TaskId) = some y := by
  show (s.tasks)[Gt.length]? = some y
  rw [h, List.getElem?_concat_length]

theorem threads_get_lastG {s : CStore E} {Gth : List Runtime.Thread} {y : Runtime.Thread}
    (h : s.threads = Gth ++ [y]) :
    ArenaField.threads.get? s (⟨Gth.length⟩ : ThreadId) = some y := by
  show (s.threads)[Gth.length]? = some y
  rw [h, List.getElem?_concat_length]

theorem callers_get_lastG {s : CStore E} {Gc : List (Caller E)} {y : Caller E}
    (h : s.callers = Gc ++ [y]) :
    ArenaField.callers.get? s (⟨Gc.length⟩ : CallerId) = some y := by
  show (s.callers)[Gc.length]? = some y
  rw [h, List.getElem?_concat_length]

theorem tasks_modify_lastG {s : CStore E} {Gt : List (Runtime.Task E)} {y : Runtime.Task E}
    (h : s.tasks = Gt ++ [y]) (f : Runtime.Task E → Runtime.Task E) :
    (ArenaField.tasks.modify s (⟨Gt.length⟩ : TaskId) f).tasks = Gt ++ [f y] := by
  show (s.tasks).modify Gt.length f = _
  rw [h, Arena.modify, modify_concat_length]

theorem insts_get_zeroG {s : CStore E} {ι : InstState} (h : s.insts = [ι]) :
    ArenaField.insts.get? s (⟨0⟩ : InstId) = some ι := by
  show (s.insts)[0]? = some ι
  rw [h]
  rfl

theorem threadIs_lastG {s : CStore E} {Gth : List Runtime.Thread} {b : TaskId}
    (h : s.threads = Gth ++ [{ task := b }]) :
    s.threadIs Runtime.Thread.waiting ⟨Gth.length⟩ = false := by
  unfold CStore.threadIs CStore.thread?
  rw [threads_get_lastG h]
  rfl

theorem threadStatus_lastG {s : CStore E} {Gth : List Runtime.Thread} {z : Runtime.Thread}
    (h : s.threads = Gth ++ [z]) (st : ThreadStatus) :
    threadStatusSt ⟨Gth.length⟩ st s = { s with threads := Gth ++ [{ z with status := st }] } := by
  obtain ⟨⟩ := s
  dsimp only at h
  subst h
  simp only [threadStatusSt, ArenaField.modify, ArenaField.threads, Arena.modify,
    modify_concat_length]

theorem setTaskState_lastG {s : CStore E} {Gt : List (Runtime.Task E)} {y : Runtime.Task E}
    (h : s.tasks = Gt ++ [y]) (st : Silmaril.Wasm.Component.AsyncRef.TaskState) :
    CStore.setTaskState ⟨Gt.length⟩ st s = { s with tasks := Gt ++ [y.withState st] } := by
  obtain ⟨⟩ := s
  dsimp only at h
  subst h
  simp only [CStore.setTaskState, ArenaField.modify, ArenaField.tasks, Arena.modify,
    modify_concat_length]

/-- Replace the store of a live run's start by an equal one. -/
theorem LRun.store_congrG {prof : ProfileKind} {hr : HostReady σ}
    {d : Call E → Canon.P E σ (Ret E)} {m M₂ : Machine.Config E σ}
    {tr : List (Label E σ)} {S' : CStore E} (h : m.store = S')
    (r : LRun prof hr d { m with store := S' } tr M₂) : LRun prof hr d m tr M₂ := by
  obtain ⟨⟩ := m
  dsimp only at h
  subst h
  exact r

/-- A task with one more thread. -/
def taskAddThread (y : Runtime.Task E) (t : ThreadId) : Runtime.Task E :=
  { y with threads := y.threads ++ [t] }

theorem registerThreadSt_eqG {s : CStore E} {Gt : List (Runtime.Task E)} {y : Runtime.Task E}
    {Gth : List Runtime.Thread} {z : Runtime.Thread} {ι ι' : InstState} {i : Nat}
    (ht : s.tasks = Gt ++ [y]) (hinst : y.inst = ⟨0⟩) (hi : s.insts = [ι])
    (hadd : ι.addThread? ⟨Gth.length⟩ = some (i, ι')) (hth : s.threads = Gth ++ [z]) :
    CStore.registerThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩ s =
      { s with
        tasks := Gt ++ [taskAddThread y ⟨Gth.length⟩]
        insts := [ι']
        threads := Gth ++ [z.withIndex i] } := by
  have h₁ : s.task? ⟨Gt.length⟩ = some y := tasks_get_lastG ht
  have h₂ : s.inst? y.inst = some ι := by rw [hinst]; exact insts_get_zeroG hi
  unfold CStore.registerThreadSt
  rw [h₁]
  dsimp only
  rw [h₂, Option.bind_some, hadd]
  dsimp only
  obtain ⟨⟩ := s
  dsimp only at ht hi hth ⊢
  subst ht hi hth
  simp only [ArenaField.modify, ArenaField.set, ArenaField.tasks, ArenaField.insts,
    ArenaField.threads, Arena.modify, Arena.set, modify_concat_length,
    show y.inst.idx = 0 by rw [hinst]]
  rfl

/-! ## Programs -/

variable [∀ a b, Decidable (E.ExternSub a b)] {impl : HostImpl E σ}

theorem runs_allocObjG {th : Option ThreadId} {α Id : Type} (F : ArenaField E Id α) (x : α)
    (m : Machine.Config E σ) (hl : (ArenaOps.allocSt F x m.store).lockdown = m.store.lockdown) :
    RunsQ (DG impl) th (allocObj F x) m [.tau, .tau] (F.mkId (F.size m.store))
      { m with store := ArenaOps.allocSt F x m.store } :=
  .get (.modify hl (.pure _ _))

theorem runs_getObjG {th : Option ThreadId} {α Id : Type} (F : ArenaField E Id α) (i : Id)
    (m : Machine.Config E σ) {x : α} (h : F.get? m.store i = some x) :
    RunsQ (DG impl) th (getObj F i) m [.tau] x m := by
  refine .get ?_
  show RunsQ _ _ (match F.get? m.store i with | some x => pure x | none => internal _) _ _ _ _
  rw [h]
  exact .pure _ _

theorem runs_modifyStoreG {th : Option ThreadId} (f : CStore E → CStore E)
    (m : Machine.Config E σ) (hl : (f m.store).lockdown = m.store.lockdown) :
    RunsQ (DG impl) th (modifyStore f) m [.tau] () { m with store := f m.store } :=
  .modify hl (.pure _ _)

theorem runs_ite_falseG {th : Option ThreadId} {b : Bool} (hb : b = false)
    (X : Canon.P E σ Unit) (m : Machine.Config E σ) :
    RunsQ (DG impl) th (if b = true then X else pure ()) m [] () m := by
  subst hb
  exact .pure _ _

theorem runs_ite_pureG {α : Type} {th : Option ThreadId} {b : Bool} (hb : b = false)
    (X : Canon.P E σ α) (a : α) (m : Machine.Config E σ) :
    RunsQ (DG impl) th (if b = true then X else pure a) m [] a m := by
  subst hb
  exact .pure _ _

theorem RunsQ.of_trG {α : Type} {th : Option ThreadId} {p : Canon.P E σ α}
    {m m' : Machine.Config E σ} {a : α} {tr tr' : List (Label E σ)}
    (h : RunsQ (DG impl) th p m tr a m') (e : tr = tr') : RunsQ (DG impl) th p m tr' a m' :=
  e ▸ h

theorem runs_enterG' {m : Machine.Config E σ} {Gt : List (Runtime.Task E)}
    {y : Runtime.Task E} {t : ThreadId} {ι ι' : InstState}
    (htasks : m.store.tasks = Gt ++ [y]) (hasync : y.ft.async_ = false) (hinst : y.inst = ⟨0⟩)
    (hinsts : m.store.insts = [ι]) (hadd : ι.addThread? t = some (1, ι')) :
    RunsQ (DG impl) (some t) (Task.enterImplicitThread Quirks.none ⟨Gt.length⟩) m
      [.tau, .tau, .tau, .tau, .tau, .tau] true
      { m with store := (CStore.registerThreadSt ⟨Gt.length⟩ t
        (CStore.setImplicitThread ⟨Gt.length⟩ t m.store)) } := by
  have h₁ : (CStore.setImplicitThread ⟨Gt.length⟩ t m.store).tasks =
      Gt ++ [{ y with implicitThread := some t }] := tasks_modify_lastG htasks _
  have hi : ArenaField.insts.get? (CStore.setImplicitThread ⟨Gt.length⟩ t m.store) y.inst =
      some ι := by
    rw [hinst]
    exact insts_get_zeroG hinsts
  unfold Task.enterImplicitThread
  apply RunsQ.of_trG
  apply RunsQ.bind (.currentThread (.pure _ _))
  apply RunsQ.bind (runs_modifyStoreG _ m rfl)
  apply RunsQ.bind (runs_getObjG ArenaField.tasks _ _ (tasks_get_lastG h₁))
  apply RunsQ.bind (runs_ite_pureG hasync _ true _)
  show RunsQ _ _ (Task.registerThread ⟨Gt.length⟩ t >>= fun _ => pure true) _ _ _ _
  apply RunsQ.bind (f := fun _ => pure true) (a := 1) ?_ (.pure _ _)
  rotate_left
  unfold Task.registerThread
  apply RunsQ.bind (runs_getObjG ArenaField.tasks _ _ (tasks_get_lastG h₁))
  apply RunsQ.bind (runs_getObjG ArenaField.insts _ _ (by exact hi))
  rw [hadd]
  exact RunsQ.bind (runs_modifyStoreG _ _
    (CStore.registerThreadSt_frame (E := E) _ _ _).2.2.2.2.2.2.1) (.pure _ _)
  rfl

/-! ## The start caller and the start task -/

/-- `mstep` at a store whose lockdown flag is a hypothesis. -/
macro "mstepG" : tactic => `(tactic| apply LRun.prog rfl (fun _ _ e => by cases e) (by assumption)
  (by first
    | exact Step.get rfl | exact Step.modify rfl | exact Step.call rfl | exact Step.popProg rfl
    | exact Step.currentThread rfl | exact Step.hostGet rfl | exact Step.hostSet rfl
    | exact Step.emit rfl
    | exact Step.resumeThread rfl rfl | exact Step.newThread rfl rfl | exact Step.threadExit rfl
    | exact Step.hostDone rfl | exact Step.callCore rfl))

theorem runs_onStartSG {th : Option ThreadId} {m : Machine.Config E σ}
    {Gc : List (Caller E)} (hc : m.store.callers = Gc ++ [.sub .start]) :
    RunsQ (DG impl) th (DG impl (.onStart ⟨Gc.length⟩)) m [.tau, .tau] (.vals []) m := by
  show RunsQ _ _ (callerOnStart Limits.spec Quirks.none ⟨Gc.length⟩) _ _ _ _
  unfold callerOnStart
  refine RunsQ.bind (tr₁ := [.tau]) (runs_getObjG ArenaField.callers _ _ (callers_get_lastG hc)) ?_
  unfold onStartProg
  exact RunsQ.bind (tr₂ := []) (runs_getObjG ArenaField.callers _ _ (callers_get_lastG hc))
    (.pure _ _)

/-- The task of the start call (root instance `0`, caller record `Gc.length`). -/
def startTask (Gc : List (Caller E)) : Runtime.Task E :=
  { ft := Instantiate.startType, opts := {}, inst := ⟨0⟩, caller := ⟨Gc.length⟩ }

/-- The task once its implicit thread `t` is registered. -/
def startTask₁ (Gc : List (Caller E)) (t : ThreadId) : Runtime.Task E :=
  taskAddThread ({ startTask Gc with implicitThread := some t } : Runtime.Task E) t

/-- The thread of the start call, running. -/
def startThread (Gt : List (Runtime.Task E)) : Runtime.Thread :=
  { status := .running, task := ⟨Gt.length⟩ }

theorem runs_startSG {th : Option ThreadId} {m : Machine.Config E σ}
    {Gt : List (Runtime.Task E)} {y : Runtime.Task E} {Gc : List (Caller E)}
    (ht : m.store.tasks = Gt ++ [y]) (hy : y.caller = ⟨Gc.length⟩)
    (hc : m.store.callers = Gc ++ [.sub .start]) :
    RunsQ (DG impl) th (Task.start ⟨Gt.length⟩) m [.tau, .tau, .tau, .tau, .tau, .tau] []
      { m with store := CStore.setTaskState ⟨Gt.length⟩ .started m.store } := by
  unfold Task.start
  apply RunsQ.of_trG
  apply RunsQ.bind (runs_getObjG ArenaField.tasks _ _ (tasks_get_lastG ht))
  apply RunsQ.bind (runs_modifyStoreG _ _ rfl)
  rw [hy]
  unfold callVals callRet perform Prog.lift
  exact RunsQ.call (runs_onStartSG hc) (.pure _ _)
  rfl

theorem runs_lower_nilG {th : Option ThreadId} (cx : LiftLowerContext E) (m : Machine.Config E σ) :
    RunsQ (DG impl) th (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams
      (([] : List Silmaril.Wasm.Component.Val).map toRefVal) (paramTypes Instantiate.startType)
      none) m [.tau] [] m := by
  rw [show paramTypes Instantiate.startType = toClosedList [] from rfl,
    lowerFlatValues_toClosed Limits.spec Quirks.none cx (max := ABI.maxFlatParams) (ts := []) (vs := []) rfl rfl
      (Nat.zero_le _)]
  exact .get (.pure _ _)

/-! ## The stores of the start call -/

/-- The store when the start thread starts running. -/
def gStore₁ (S : CStore E) (a : E.FuncAddr) : CStore E :=
  { S with
    funcs := S.funcs ++ [.lifted a Instantiate.startType {} ⟨0⟩]
    callers := S.callers ++ [.sub .start]
    tasks := S.tasks ++ [startTask S.callers]
    threads := S.threads ++ [startThread S.tasks] }

/-- The store once the start thread entered its task. -/
def gStore₂ (S : CStore E) (a : E.FuncAddr) (ι' : InstState) : CStore E :=
  { gStore₁ S a with
    tasks := S.tasks ++ [startTask₁ S.callers ⟨S.threads.length⟩]
    insts := [ι']
    threads := S.threads ++ [(startThread S.tasks).withIndex 1] }

/-- The store when the core activation of the start function begins. -/
def gStore₃ (S : CStore E) (a : E.FuncAddr) (ι' : InstState) : CStore E :=
  { gStore₂ S a ι' with
    tasks := S.tasks ++ [(startTask₁ S.callers ⟨S.threads.length⟩).withState .started] }

/-- **The start call reaches the core activation of the start function**: from the
instantiation program at `runStart ⟨0⟩ a` (root instance `0`, its only instance), a live run
to the core activation `E.invoke a []`, the core store and the lockdown flag unchanged. -/
theorem start_coreG (prof : ProfileKind) (M : Machine.Config E σ) (a : E.FuncAddr)
    (ι ι' : InstState) {th : Option ThreadId} {K : Unit → Canon.P E σ (Ret E)}
    {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    (hc : M.ctl = ⟨th, .prog (Instantiate.runStart ⟨0⟩ a >>= K), segs⟩ :: rest)
    (hl : M.store.lockdown = false) (hi : M.store.insts = [ι])
    (hadd : ι.addThread? ⟨M.store.threads.length⟩ = some (1, ι')) :
    ∃ M₀ thc Kc segsc restc tr, LRun prof (fun _ _ => false) (DG impl) M tr M₀ ∧
      M₀.ctl = ⟨thc, .core (E.invoke a []) Kc, segsc⟩ :: restc ∧
      M₀.store.core = M.store.core ∧ M₀.store.lockdown = false := by
  obtain ⟨S, h₀, ctl₀, conts, pending, results, cancels⟩ := M
  dsimp only at hc hl hi hadd ⊢
  subst hc
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_⟩
  apply RunsQ.chunk2 rfl (runs_allocObjG ArenaField.funcs (.lifted a Instantiate.startType {} ⟨0⟩) _ rfl) hl
  apply RunsQ.chunk2 rfl (runs_allocObjG ArenaField.callers (.sub .start) _ rfl) hl
  apply LRun.prog rfl (fun _ _ e => by cases e) hl (.call rfl)
  have hget : ArenaField.funcs.get? (gStore₁ S a) (⟨S.funcs.length⟩ : FuncId) =
      some (.lifted a Instantiate.startType {} ⟨0⟩) := by
    show (S.funcs ++ [_])[S.funcs.length]? = _
    rw [List.getElem?_concat_length]
  apply RunsQ.chunk rfl (runs_getObjG ArenaField.funcs _ _ hget) hl
  apply RunsQ.chunk rfl (runs_allocObjG ArenaField.tasks _ _ rfl) hl
  apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) hl
  apply RunsQ.chunk2 rfl (RunsQ.get (.pure _ _)) hl
  apply RunsQ.chunk2 rfl (runs_ite_falseG (by exact threadIs_lastG rfl) _ _) hl
  apply LRun.prog rfl (fun _ _ e => by cases e) hl
    (.resumeThread rfl (by exact Config.cont?_setCont_self _ _ _))
  have e₁ : ∀ S' : CStore E, S'.threads = S.threads ++ [{ task := ⟨S.tasks.length⟩ }] →
      threadStatusSt ⟨S.threads.length⟩ .running S' =
        { S' with threads := S.threads ++ [startThread S.tasks] } :=
    fun S' h => threadStatus_lastG h _
  apply LRun.store_congrG (S' := gStore₁ S a) ((e₁ _ rfl).trans rfl)
  have hS₁ : (gStore₁ S a).insts = [ι] := hi
  apply RunsQ.chunk (th := some ⟨S.threads.length⟩)
    (p := Task.enterImplicitThread Quirks.none ⟨S.tasks.length⟩) (a := true) rfl
    (runs_enterG' (Gt := S.tasks) (y := startTask S.callers) rfl rfl rfl hS₁ hadd) hl
  have e₂ : CStore.registerThreadSt ⟨S.tasks.length⟩ ⟨S.threads.length⟩
      (CStore.setImplicitThread ⟨S.tasks.length⟩ ⟨S.threads.length⟩ (gStore₁ S a)) =
        gStore₂ S a ι' :=
    registerThreadSt_eqG (tasks_modify_lastG rfl _) rfl hS₁ hadd rfl
  apply LRun.store_congrG (S' := gStore₂ S a ι') (by exact e₂)
  have hS₂ : (gStore₂ S a ι').tasks = S.tasks ++ [startTask₁ S.callers ⟨S.threads.length⟩] :=
    rfl
  apply RunsQ.chunk rfl (runs_getObjG ArenaField.tasks _ _ (tasks_get_lastG (Gt := S.tasks) hS₂))
    hl
  apply RunsQ.chunk rfl (runs_startSG (Gt := S.tasks) (Gc := S.callers) hS₂ rfl rfl) hl
  apply RunsQ.chunk rfl (runs_lower_nilG _ _) hl
  apply LRun.store_congrG (S' := gStore₃ S a ι') (by
    exact setTaskState_lastG (Gt := S.tasks) (y := startTask₁ S.callers ⟨S.threads.length⟩)
      rfl _)
  mstepG
  exact .refl _
  · rfl
  · rfl
  · exact hl

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
