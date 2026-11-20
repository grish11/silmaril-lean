module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Path
public import Silmaril.Proofs.Wasm.Component.Reference.FlatABI

/-!
# The start call during instantiation, with its epilogue, over any engine

`FirstImp.Path.start_coreX` runs `Instantiate.runStart ⟨0⟩ a` to the core activation of the
start function over any engine and host. `Reference.StartICall.start_atA` also runs the
**epilogue** (from the return of the core activation back to the instantiation program), but over
`core3P P`, under the answering host, and only when the start function made no host call. This
file restates the epilogue over any engine `E` and host functions `impl` (dispatcher `DG impl`),
when the start function's host calls have added subtasks `xs` and caller records `cs` to the store
and moved the host state to `h`:

* `runs_returnSG`, `runs_exitG`, `runs_callUnit_loopG`, …: the programs of the epilogue
  (`Task.return_` reading the start caller record by its index, `exit_implicit_thread`, the
  synchronous lift loop);
* `start_atG`: from `runStart ⟨0⟩ a`, a live run to the core activation of `E.invoke a []`
  (`StartAtG.ctl`, `.store`, `.host`); from its return with no values, for any core store `y.1`,
  host state `h`, subtasks `xs` and caller records `cs`, a live run back to the instantiation
  program `K ()` at `startedCfgG M a ι' y.1 h xs cs` (`StartAtG.ret`): the start task finished,
  its thread exited, the start caller record kept.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs

variable {E : CoreEngine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)] {impl : HostImpl E σ}

/-! ## The programs of the epilogue -/

theorem runs_onResolveSG {th : Option ThreadId} {m : Machine.Config E σ} {c : CallerId}
    (r : Option (List Silmaril.Wasm.Component.Reference.Val))
    (hc : ArenaField.callers.get? m.store c = some (.sub .start)) :
    RunsQ (DG impl) th (DG impl (.onResolve c r)) m [.tau, .tau] .unit m := by
  show RunsQ _ _ (callerOnResolve Limits.spec Quirks.none c r) _ _ _ _
  unfold callerOnResolve
  refine RunsQ.bind (tr₁ := [.tau]) (runs_getObjG ArenaField.callers _ _ hc) ?_
  unfold onResolveProg
  exact RunsQ.bind (tr₂ := []) (runs_getObjG ArenaField.callers _ _ hc) (.pure _ _)

theorem runs_trapIfG {th : Option ThreadId} {b : Bool} (hb : b = false) (r : TrapReason)
    (m : Machine.Config E σ) : RunsQ (DG impl) th (trapIf b r) m [] () m := by
  subst hb
  exact .pure _ _

theorem runs_returnSG {th : Option ThreadId} {m : Machine.Config E σ}
    {Gt : List (Runtime.Task E)} {y : Runtime.Task E}
    (vs : List Silmaril.Wasm.Component.Reference.Val) (ht : m.store.tasks = Gt ++ [y])
    (hst : y.state = .started) (hb : y.numBorrows = 0)
    (hc : ArenaField.callers.get? m.store y.caller = some (.sub .start)) :
    RunsQ (DG impl) th (Task.return_ ⟨Gt.length⟩ vs) m
      [.tau, .tau, .tau, .tau, .tau, .tau] ()
      { m with store := CStore.setTaskState ⟨Gt.length⟩ .resolved m.store } := by
  unfold Task.return_
  apply RunsQ.of_trG
  apply RunsQ.bind (runs_getObjG ArenaField.tasks _ _ (tasks_get_lastG ht))
  apply RunsQ.bind (runs_trapIfG (by rw [hst]; rfl) _ _)
  apply RunsQ.bind (runs_trapIfG (by rw [hb]; rfl) _ _)
  unfold callUnit callRet perform Prog.lift
  apply RunsQ.bind (RunsQ.call (runs_onResolveSG (some vs) hc) (.pure _ _))
  exact runs_modifyStoreG _ _ rfl
  rfl

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem unregisterThreadSt_eqG {s : CStore E} {Gt : List (Runtime.Task E)}
    {y : Runtime.Task E} {ι : InstState} (t : ThreadId) (i : Nat)
    (ht : s.tasks = Gt ++ [y]) (hinst : y.inst = ⟨0⟩) (hi : s.insts = [ι]) :
    CStore.unregisterThreadSt ⟨Gt.length⟩ t i s =
      { s with
        tasks := Gt ++ [{ y with threads := y.threads.erase t }]
        insts := [InstState.removeThread i ι] } := by
  have h₁ : s.task? ⟨Gt.length⟩ = some y := tasks_get_lastG ht
  unfold CStore.unregisterThreadSt
  rw [h₁]
  obtain ⟨⟩ := s
  dsimp only at ht hi ⊢
  subst ht hi
  simp only [ArenaField.modify, ArenaField.tasks, ArenaField.insts, Arena.modify,
    modify_concat_length, show y.inst.idx = 0 by rw [hinst]]
  rfl

theorem runs_unregisterG {th : Option ThreadId} {m : Machine.Config E σ}
    {Gt : List (Runtime.Task E)} {y : Runtime.Task E} {Gth : List Runtime.Thread}
    {z : Runtime.Thread} {ι ι' : InstState} {i : Nat} {t' : ThreadId}
    (ht : m.store.tasks = Gt ++ [y]) (hst : y.state = .resolved)
    (hthr : m.store.threads = Gth ++ [z]) (hidx : z.index = some i) (hinst : y.inst = ⟨0⟩)
    (hinsts : m.store.insts = [ι]) (hrem : ι.removeThread? i = some (t', ι')) :
    RunsQ (DG impl) th (Task.unregisterThread ⟨Gt.length⟩ ⟨Gth.length⟩) m
      [.tau, .tau, .tau, .tau] ()
      { m with store := CStore.unregisterThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩ i m.store } := by
  have hi : ArenaField.insts.get? m.store y.inst = some ι := by
    rw [hinst]
    exact insts_get_zeroG hinsts
  unfold Task.unregisterThread
  apply RunsQ.of_trG
  apply RunsQ.bind (runs_getObjG ArenaField.tasks _ _ (tasks_get_lastG ht))
  apply RunsQ.bind (runs_trapIfG (by rw [hst]; simp) _ _)
  apply RunsQ.bind (runs_getObjG ArenaField.threads _ _ (threads_get_lastG hthr))
  rw [hidx]
  apply RunsQ.bind (.pure _ _)
  apply RunsQ.bind (runs_getObjG ArenaField.insts _ _ hi)
  rw [hrem]
  exact runs_modifyStoreG _ _ (CStore.unregisterThreadSt_frame (E := E) _ _ _ _).2.2.2.2.2.2.2.1
  rfl

theorem runs_exitG {th : Option ThreadId} {m : Machine.Config E σ}
    {Gt : List (Runtime.Task E)} {y : Runtime.Task E} {Gth : List Runtime.Thread}
    {z : Runtime.Thread} {ι ι' : InstState} {i : Nat} {t' : ThreadId}
    (ht : m.store.tasks = Gt ++ [y]) (himp : y.implicitThread = some ⟨Gth.length⟩)
    (hst : y.state = .resolved) (hasync : y.ft.async_ = false)
    (hthr : m.store.threads = Gth ++ [z]) (hidx : z.index = some i) (hinst : y.inst = ⟨0⟩)
    (hinsts : m.store.insts = [ι]) (hrem : ι.removeThread? i = some (t', ι')) :
    RunsQ (DG impl) th (Task.exitImplicitThread ⟨Gt.length⟩) m [.tau, .tau, .tau, .tau, .tau] ()
      { m with store := CStore.unregisterThreadSt ⟨Gt.length⟩ ⟨Gth.length⟩ i m.store } := by
  have hu := runs_unregisterG (impl := impl) (th := th) ht hst hthr hidx hinst hinsts hrem
  unfold Task.exitImplicitThread
  apply RunsQ.of_trG
  apply RunsQ.bind (runs_getObjG ArenaField.tasks _ _ (tasks_get_lastG ht))
  rw [himp]
  apply RunsQ.bind (.pure _ _)
  apply RunsQ.bind hu
  exact runs_ite_falseG (by rw [hasync]; rfl) _ _
  rfl

theorem runs_loopG {th : Option ThreadId} {m : Machine.Config E σ}
    {Gt : List (Runtime.Task E)} {y : Runtime.Task E}
    (ht : m.store.tasks = Gt ++ [y]) (hst : y.state = .resolved) :
    RunsQ (DG impl) th (DG impl (.loop (.syncLiftLoop ⟨Gt.length⟩))) m [.tau] .unit m := by
  show RunsQ _ _ (syncLiftLoopBody (fun _ _ => false) ⟨Gt.length⟩) _ _ _ _
  unfold syncLiftLoopBody
  apply RunsQ.bind (tr₂ := []) (runs_getObjG ArenaField.tasks _ _ (tasks_get_lastG ht))
  rw [hst]
  exact .pure _ _

theorem runs_callUnit_loopG {th : Option ThreadId} {m : Machine.Config E σ}
    {Gt : List (Runtime.Task E)} {y : Runtime.Task E}
    (ht : m.store.tasks = Gt ++ [y]) (hst : y.state = .resolved) :
    RunsQ (DG impl) th (callUnit (.loop (.syncLiftLoop ⟨Gt.length⟩))) m [.tau, .tau, .tau] () m := by
  unfold callUnit callRet perform Prog.lift
  exact RunsQ.call (runs_loopG ht hst) (.pure _ _)

theorem runs_lift_nilG {th : Option ThreadId} (cx : LiftLowerContext E) (m : Machine.Config E σ) :
    ∃ c, RunsQ (DG impl) th (liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList []) (resultTypes Instantiate.startType)) m [.tau] ([], c) m := by
  rw [show resultTypes Instantiate.startType = toClosedList [] from rfl,
    show FlatCursor.ofList ([] : List FlatValue) = ⟨[], 0⟩ from rfl,
    liftFlatValues_toClosed (max := ABI.maxFlatResults) (ts := []) Limits.spec Quirks.none cx
      (Nat.zero_le _)]
  exact ⟨_, .get (.pure _ _)⟩

/-! ## The stores of the epilogue -/

section Stores

variable (E) in
/-- The start task once finished: resolved, its implicit thread `t` unregistered. -/
def startTaskEnd (Gc : List (Caller E)) (t : ThreadId) : Runtime.Task E :=
  { ((startTask₁ Gc t).withState .started).withState .resolved with
    threads := (((startTask₁ Gc t).withState .started).withState .resolved).threads.erase t }

/-- The store when the core activation of the start function returns: core store `cs'`, the
host calls' subtasks `xs` and caller records `cs` appended. -/
def gStore₃X (S : CStore E) (a : E.FuncAddr) (ι' : InstState) (cs' : E.Store (CanonHost E))
    (xs : List Subtask) (cs : List (Caller E)) : CStore E :=
  { gStore₃ S a ι' with
    core := cs'
    subtasks := S.subtasks ++ xs
    callers := S.callers ++ [.sub .start] ++ cs }

/-- The store when the start task resolved. -/
def gStore₄X (S : CStore E) (a : E.FuncAddr) (ι' : InstState) (cs' : E.Store (CanonHost E))
    (xs : List Subtask) (cs : List (Caller E)) : CStore E :=
  { gStore₃X S a ι' cs' xs cs with
    tasks := S.tasks ++ [((startTask₁ S.callers ⟨S.threads.length⟩).withState .started).withState
      .resolved] }

/-- **The store after the start function.** -/
def gStore₅X (S : CStore E) (a : E.FuncAddr) (ι' : InstState) (cs' : E.Store (CanonHost E))
    (xs : List Subtask) (cs : List (Caller E)) : CStore E :=
  { gStore₄X S a ι' cs' xs cs with
    tasks := S.tasks ++ [startTaskEnd E S.callers ⟨S.threads.length⟩]
    insts := [InstState.removeThread 1 ι']
    threads := S.threads ++ [{ (startThread S.tasks).withIndex 1 with status := .exited }] }

variable (impl) in
/-- **The configuration after the start function**, back in the instantiation program. -/
def startedCfgG (M : Machine.Config E σ) (a : E.FuncAddr) (ι' : InstState)
    (cs' : E.Store (CanonHost E)) (h : σ) (xs : List Subtask) (cs : List (Caller E)) :
    Machine.Config E σ :=
  { M with
    host := h
    store := gStore₅X M.store a ι' cs' xs cs
    conts := Config.setSlot (Config.setSlot M.conts M.store.threads.length
      (some (threadAct (DG impl) ⟨M.store.threads.length⟩
        (.liftImplicit ⟨M.store.tasks.length⟩ a)))) M.store.threads.length none }

end Stores

/-! ## The start call -/

variable (impl) in
/-- The configuration `M₀` runs the core activation of the start function `a`; from its return
with no values, after host calls that moved the host state to `h` and added the subtasks `xs` and
the caller records `cs`, the run goes back to the instantiation program `K ()`. -/
structure StartAtG (prof : ProfileKind) (M : Machine.Config E σ) (a : E.FuncAddr)
    (ι' : InstState) (th : Option ThreadId) (K : Unit → Canon.P E σ (Ret E))
    (segs : List (Seg E σ)) (rest : List (Activation E σ))
    (M₀ : Machine.Config E σ) (thc : Option ThreadId)
    (Kc : List FlatValue → Canon.P E σ (Ret E)) (segsc : List (Seg E σ))
    (restc : List (Activation E σ)) : Prop where
  ctl : M₀.ctl = ⟨thc, .core (E.invoke a []) Kc, segsc⟩ :: restc
  store : M₀.store = gStore₃ M.store a ι'
  thread : thc = some ⟨M.store.threads.length⟩
  host : M₀.host = M.host
  ret : ∀ (y : CoreSt E) (h : σ) (xs : List Subtask) (cs : List (Caller E)), ∃ tr,
    LRun prof (fun _ _ => false) (DG impl)
      (retCfg { M₀ with host := h, store := { M₀.store with
          subtasks := M₀.store.subtasks ++ xs, callers := M₀.store.callers ++ cs } }
        thc Kc segsc restc y [])
      tr { startedCfgG impl M a ι' y.1 h xs cs with ctl := ⟨th, .prog (K ()), segs⟩ :: rest } ∧
    traceObs tr = []

/-- **The start call with its epilogue**, over any engine and host. -/
theorem start_atG (prof : ProfileKind) (M : Machine.Config E σ) (a : E.FuncAddr)
    (ι ι' : InstState) {th : Option ThreadId} {K : Unit → Canon.P E σ (Ret E)}
    {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    (hc : M.ctl = ⟨th, .prog (Instantiate.runStart ⟨0⟩ a >>= K), segs⟩ :: rest)
    (hl : M.store.lockdown = false) (hi : M.store.insts = [ι])
    (hadd : ι.addThread? ⟨M.store.threads.length⟩ = some (1, ι'))
    (hrem : ι'.removeThread? 1 = some (⟨M.store.threads.length⟩, InstState.removeThread 1 ι')) :
    ∃ M₀ thc Kc segsc restc tr, LRun prof (fun _ _ => false) (DG impl) M tr M₀ ∧
      traceObs tr = [] ∧ StartAtG impl prof M a ι' th K segs rest M₀ thc Kc segsc restc := by
  obtain ⟨S, h₀, ctl₀, conts, pending, results, cancels⟩ := M
  dsimp only at hc hl hi hadd hrem ⊢
  subst hc
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  · apply RunsQ.chunk2 rfl (runs_allocObjG ArenaField.funcs (.lifted a Instantiate.startType {} ⟨0⟩) _ rfl) hl
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
  apply And.intro
  · simp [traceObs, Label.obs?]
  · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro y h xs cs
    apply Exists.intro
    refine ⟨?_, ?_⟩
    · apply LRun.store_congrG (S' := gStore₃X S a ι' y.1 xs cs) rfl
      have hS₃ : (gStore₃X S a ι' y.1 xs cs).tasks =
          S.tasks ++ [(startTask₁ S.callers ⟨S.threads.length⟩).withState .started] := rfl
      have hcl : ArenaField.callers.get? (gStore₃X S a ι' y.1 xs cs) (⟨S.callers.length⟩ : CallerId) =
          some (.sub .start) := by
        show (S.callers ++ [.sub .start] ++ cs)[S.callers.length]? = _
        rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      unfold retCfg
      apply RunsQ.chunk2 rfl (runs_lift_nilG (impl := impl) _ _).choose_spec hl
      apply RunsQ.chunk2 rfl (runs_returnSG (Gt := S.tasks) _ hS₃ rfl rfl hcl) hl
      apply LRun.store_congrG (S' := gStore₄X S a ι' y.1 xs cs)
        (by refine setTaskState_lastG (Gt := S.tasks) ?_ _; rfl)
      apply RunsQ.chunk rfl
        (runs_exitG (impl := impl) (Gt := S.tasks) (Gth := S.threads)
          (y := ((startTask₁ S.callers ⟨S.threads.length⟩).withState .started).withState .resolved)
          (z := (startThread S.tasks).withIndex 1) (ι := ι') rfl rfl rfl rfl rfl rfl rfl rfl hrem) hl
      have e₄ : CStore.unregisterThreadSt ⟨S.tasks.length⟩ ⟨S.threads.length⟩ 1
          (gStore₄X S a ι' y.1 xs cs) =
            { gStore₄X S a ι' y.1 xs cs with
              tasks := S.tasks ++ [startTaskEnd E S.callers ⟨S.threads.length⟩]
              insts := [InstState.removeThread 1 ι'] } :=
        unregisterThreadSt_eqG _ _ rfl rfl rfl
      apply LRun.store_congrG (S' := { gStore₄X S a ι' y.1 xs cs with
          tasks := S.tasks ++ [startTaskEnd E S.callers ⟨S.threads.length⟩]
          insts := [InstState.removeThread 1 ι'] }) e₄
      mstepG
      have e₅ : threadStatusSt ⟨S.threads.length⟩ .exited
          { gStore₄X S a ι' y.1 xs cs with
            tasks := S.tasks ++ [startTaskEnd E S.callers ⟨S.threads.length⟩]
            insts := [InstState.removeThread 1 ι'] } = gStore₅X S a ι' y.1 xs cs :=
        threadStatus_lastG (z := (startThread S.tasks).withIndex 1) rfl _
      apply LRun.store_congrG (S' := gStore₅X S a ι' y.1 xs cs) e₅
      apply RunsQ.chunk rfl (runs_callUnit_loopG (impl := impl) (Gt := S.tasks) rfl rfl) hl
      repeat mstepG
      exact .refl _
    · simp [traceObs, Label.obs?]

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
