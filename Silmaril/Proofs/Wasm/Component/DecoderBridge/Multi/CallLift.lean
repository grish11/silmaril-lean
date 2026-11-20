module

public import Silmaril.Wasm.Component.DecoderBridge.MultiX.Defs
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Start
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.LaterCore
public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.RefRun

/-!
# A top-level call of an option-less `canon lift` of `func() -> u32`

`Multi.Start` runs the start call of an instantiation over any engine and host. This file runs a
**top-level call** (the host event `invokeTop`) of the option-less lift (instance `0`) at the
type `func() -> u32` of a core function, over any engine `E` and host functions `impl`, from any
configuration between calls (host in control, no lockdown, nesting depth `0`, one component
instance whose thread table admits the call's thread):

* `runs_onStartHG`, `runs_onResolveHG`, `runs_startHG`, `runs_returnHG`: the programs of the host
  caller record (`Caller.host c [] 0`), emitting `started c` and `resolved c`;
* `invoke_atG`: from the configuration after the invoke, a live run to the core activation
  `E.invoke a []` (the core store, the lockdown flag and the host state unchanged); from its return
  with one `i32` `v`, a live run to a configuration with the host in control, no lockdown, the
  host state unchanged and call `c` resolved with `u32 v`;
* `callLift`: **`Task.callLift`** over `core3 neverFail` with the logging host `embL`: a host-free
  run of the core function (`CoreEngine.Steps`) is a run of the core activation in the machine
  (`core3`'s internal step is only enabled at `running` threads), so the session call resolves.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs

/-- The reference function type `func() -> u32`. -/
def tyU32 : Types.FuncType RtId := { params := [], result := some (.prim .u32), async_ := false }

section Generic

variable {E : CoreEngine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)] {impl : HostImpl E σ}

/-! ## The host caller record -/

theorem runs_onStartHG {th : Option ThreadId} {m : Machine.Config E σ} {cid : CallerId}
    {c : CallId} {args : List Silmaril.Wasm.Component.Reference.Val}
    (hc : ArenaField.callers.get? m.store cid = some (.host c args 0)) :
    RunsQ (DG impl) th (DG impl (.onStart cid)) m [.tau, .obs (.started c)] (.vals args) m := by
  show RunsQ _ _ (callerOnStart Limits.spec Quirks.none cid) _ _ _ _
  unfold callerOnStart
  exact RunsQ.bind (runs_getObjG ArenaField.callers _ _ hc)
    (RunsQ.bind (tr₁ := [.obs (.started c)]) (.emit (.pure _ _)) (.pure _ _))

theorem runs_onResolveHG {th : Option ThreadId} {m : Machine.Config E σ} {cid : CallerId}
    {c : CallId} {args : List Silmaril.Wasm.Component.Reference.Val}
    (r : Option (List Silmaril.Wasm.Component.Reference.Val))
    (hc : ArenaField.callers.get? m.store cid = some (.host c args 0)) :
    RunsQ (DG impl) th (DG impl (.onResolve cid r)) m [.tau, .obs (.resolved c r)] .unit
      (m.resolve c r) := by
  show RunsQ _ _ (callerOnResolve Limits.spec Quirks.none cid r) _ _ _ _
  unfold callerOnResolve
  exact RunsQ.bind (runs_getObjG ArenaField.callers _ _ hc)
    (RunsQ.bind (tr₁ := [.obs (.resolved c r)]) (.emit (.pure _ _)) (.pure _ _))

theorem runs_startHG {th : Option ThreadId} {m : Machine.Config E σ}
    {Gt : List (Runtime.Task E)} {y : Runtime.Task E} {c : CallId}
    {args : List Silmaril.Wasm.Component.Reference.Val} (ht : m.store.tasks = Gt ++ [y])
    (hc : ArenaField.callers.get? m.store y.caller = some (.host c args 0)) :
    RunsQ (DG impl) th (Task.start ⟨Gt.length⟩) m
      [.tau, .tau, .tau, .tau, .obs (.started c), .tau] args
      { m with store := CStore.setTaskState ⟨Gt.length⟩ .started m.store } := by
  unfold Task.start
  apply RunsQ.of_trG
  apply RunsQ.bind (runs_getObjG ArenaField.tasks _ _ (tasks_get_lastG ht))
  apply RunsQ.bind (runs_modifyStoreG _ _ rfl)
  unfold callVals callRet perform Prog.lift
  exact RunsQ.call (runs_onStartHG hc) (.pure _ _)
  rfl

theorem runs_returnHG {th : Option ThreadId} {m : Machine.Config E σ}
    {Gt : List (Runtime.Task E)} {y : Runtime.Task E} {c : CallId}
    {args : List Silmaril.Wasm.Component.Reference.Val}
    (vs : List Silmaril.Wasm.Component.Reference.Val) (ht : m.store.tasks = Gt ++ [y])
    (hst : y.state = .started) (hb : y.numBorrows = 0)
    (hc : ArenaField.callers.get? m.store y.caller = some (.host c args 0)) :
    RunsQ (DG impl) th (Task.return_ ⟨Gt.length⟩ vs) m
      [.tau, .tau, .tau, .obs (.resolved c (some vs)), .tau, .tau] ()
      { m.resolve c (some vs) with
        store := CStore.setTaskState ⟨Gt.length⟩ .resolved m.store } := by
  unfold Task.return_
  apply RunsQ.of_trG
  apply RunsQ.bind (runs_getObjG ArenaField.tasks _ _ (tasks_get_lastG ht))
  apply RunsQ.bind (runs_trapIfG (by rw [hst]; rfl) _ _)
  apply RunsQ.bind (runs_trapIfG (by rw [hb]; rfl) _ _)
  unfold callUnit callRet perform Prog.lift
  apply RunsQ.bind (RunsQ.call (runs_onResolveHG (some vs) hc) (.pure _ _))
  exact runs_modifyStoreG _ _ rfl
  rfl

end Generic

/-! ## The stores of the call -/

section Stores

variable {E : CoreEngine}

/-- The task of the call (instance `0`, caller record `S.callers.length`). -/
def callTask (S : CStore E) (ty : Types.FuncType RtId) : Runtime.Task E :=
  { ft := ty, opts := {}, inst := ⟨0⟩, caller := ⟨S.callers.length⟩ }

/-- The task once its implicit thread `t` is registered. -/
def callTask₁ (S : CStore E) (ty : Types.FuncType RtId) (t : ThreadId) : Runtime.Task E :=
  taskAddThread ({ callTask S ty with implicitThread := some t } : Runtime.Task E) t

/-- The task once finished: resolved, its implicit thread `t` unregistered. -/
def callTaskEnd (S : CStore E) (ty : Types.FuncType RtId) (t : ThreadId) : Runtime.Task E :=
  { ((callTask₁ S ty t).withState .started).withState .resolved with
    threads := (((callTask₁ S ty t).withState .started).withState .resolved).threads.erase t }

/-- The store when the thread of the call starts running. -/
def iStore₁ (S : CStore E) (c : CallId) (ty : Types.FuncType RtId) : CStore E :=
  { S with
    callers := S.callers ++ [.host c [] 0]
    nestingDepth := S.nestingDepth + 1
    tasks := S.tasks ++ [callTask S ty]
    threads := S.threads ++ [startThread S.tasks] }

/-- The store once the thread entered its task. -/
def iStore₂ (S : CStore E) (c : CallId) (ty : Types.FuncType RtId) (ι' : InstState) :
    CStore E :=
  { iStore₁ S c ty with
    tasks := S.tasks ++ [callTask₁ S ty ⟨S.threads.length⟩]
    insts := [ι']
    threads := S.threads ++ [(startThread S.tasks).withIndex 1] }

/-- The store when the core activation begins, with core store `cs'`. -/
def iStore₃ (S : CStore E) (c : CallId) (ty : Types.FuncType RtId) (ι' : InstState)
    (cs' : E.Store (CanonHost E)) : CStore E :=
  { iStore₂ S c ty ι' with
    core := cs'
    tasks := S.tasks ++ [(callTask₁ S ty ⟨S.threads.length⟩).withState .started] }

/-- The store when the task resolved. -/
def iStore₄ (S : CStore E) (c : CallId) (ty : Types.FuncType RtId) (ι' : InstState)
    (cs' : E.Store (CanonHost E)) : CStore E :=
  { iStore₃ S c ty ι' cs' with
    tasks := S.tasks ++ [((callTask₁ S ty ⟨S.threads.length⟩).withState .started).withState
      .resolved] }

/-- The store when the thread of the call exited. -/
def iStore₅ (S : CStore E) (c : CallId) (ty : Types.FuncType RtId) (ι' : InstState)
    (cs' : E.Store (CanonHost E)) : CStore E :=
  { iStore₄ S c ty ι' cs' with
    tasks := S.tasks ++ [callTaskEnd S ty ⟨S.threads.length⟩]
    insts := [InstState.removeThread 1 ι']
    threads := S.threads ++ [{ (startThread S.tasks).withIndex 1 with status := .exited }] }

end Stores

/-! ## The call -/

section Call

variable {E : CoreEngine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)] {impl : HostImpl E σ}

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- A host frame of call `c` returning its `on_cancel` at the bottom of the chain. -/
theorem hostFinish_cancelG (m : Machine.Config E σ)
    (Pd : List (CallId × FuncId × List Silmaril.Wasm.Component.Reference.Val))
    (c : CallId) (f : FuncId) (args : List Silmaril.Wasm.Component.Reference.Val)
    (cr : CancelRef) (hp : m.pending = Pd ++ [(c, f, args)]) :
    hostFinish (.cancel cr) [] m = ({ m with ctl := [] } : Machine.Config E σ).setCancel c cr := by
  have hl : lastCall? m = some c := by
    unfold lastCall?
    rw [hp, List.getLast?_concat]
    rfl
  unfold hostFinish
  rw [hl]

/-- The configuration after the host invoked `f` with no arguments as top-level call `c`. -/
def invokedG (M : Machine.Config E σ) (c : CallId) (f : FuncId) : Machine.Config E σ :=
  { M with pending := M.pending ++ [(c, f, [])], ctl := [.ofProg none (StepDefs.invokeProg c f [])] }

theorem runs_lower_nilU {th : Option ThreadId} (cx : LiftLowerContext E)
    (m : Machine.Config E σ) :
    RunsQ (DG impl) th (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams
      ([] : List Silmaril.Wasm.Component.Reference.Val) (paramTypes tyU32) none) m [.tau] [] m := by
  rw [show paramTypes tyU32 = toClosedList [] from rfl,
    show ([] : List Silmaril.Wasm.Component.Reference.Val) =
      ([] : List Silmaril.Wasm.Component.Val).map toRefVal from rfl,
    lowerFlatValues_toClosed Limits.spec Quirks.none cx (max := ABI.maxFlatParams) (ts := [])
      (vs := []) rfl rfl (Nat.zero_le _)]
  exact .get (.pure _ _)

theorem runs_lift_u32G {th : Option ThreadId} (cx : LiftLowerContext E) (m : Machine.Config E σ)
    (v : BitVec 32) :
    ∃ c, RunsQ (DG impl) th (liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList [⟨.int .i32, v⟩]) (resultTypes tyU32)) m [.tau]
      ([toRefVal (.u32 v)], c) m := by
  have h := liftFlatTypes_liftArgs (σ := σ) (E := E) Limits.spec Quirks.none cx
    (ptrTypeIn m.store cx) (ts := [.u32]) (ys := [⟨.int .i32, v⟩]) rfl rfl
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rw [show resultTypes tyU32 = toClosedList [.u32] from rfl,
    show FlatCursor.ofList ([⟨.int .i32, v⟩] : List FlatValue) = ⟨[⟨.int .i32, v⟩], 0⟩ from rfl,
    liftFlatValues_toClosed (max := ABI.maxFlatResults) Limits.spec Quirks.none cx (by decide)]
  refine .get ?_
  show RunsQ _ _ (liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn m.store cx)
    (toClosedList [.u32]) ⟨[⟨.int .i32, v⟩], 0⟩) _ _ _ _
  rw [hc]
  exact .pure _ _

/-- **A top-level call of the option-less lift of `func() -> u32`**: from the configuration after
the invoke, a live run to the core activation of `a` (core store, lockdown flag, host state and
resolutions unchanged); from its return with one `i32` `v`, a live run to the host in control,
the call resolved with `u32 v`. -/
theorem invoke_atG (prof : ProfileKind) (M : Machine.Config E σ) (c : CallId) (f : FuncId)
    (a : E.FuncAddr) (ι ι' : InstState) (hl : M.store.lockdown = false)
    (hi : M.store.insts = [ι])
    (hf : ArenaField.funcs.get? M.store f = some (.lifted a tyU32 {} ⟨0⟩))
    (hadd : ι.addThread? ⟨M.store.threads.length⟩ = some (1, ι'))
    (hrem : ι'.removeThread? 1 = some (⟨M.store.threads.length⟩, InstState.removeThread 1 ι')) :
    ∃ M₀ thc Kc segsc restc tr, LRun prof (fun _ _ => false) (DG impl) (invokedG M c f) tr M₀ ∧
      M₀.ctl = ⟨thc, .core (E.invoke a []) Kc, segsc⟩ :: restc ∧
      M₀.store.core = M.store.core ∧ M₀.store.lockdown = false ∧
      ∀ (y : CoreSt E) (v : BitVec 32), ∃ tr' M', LRun prof (fun _ _ => false) (DG impl)
        (retCfg M₀ thc Kc segsc restc y [⟨.int .i32, v⟩]) tr' M' ∧
        M'.ctl = [] ∧ M'.store.lockdown = false ∧ M'.host = M.host ∧
        M'.results = M.results ++ [(c, some [toRefVal (.u32 v)])] := by
  obtain ⟨S, h₀, ctl₀, conts, pending, results, cancels⟩ := M
  dsimp only at hl hi hf hadd hrem ⊢
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  · unfold invokedG
    apply RunsQ.chunk rfl (runs_allocObjG ArenaField.callers (.host c [] 0) _ rfl) hl
    apply RunsQ.chunk rfl (runs_modifyStoreG (f := enterHostSt) _ rfl) hl
    apply LRun.prog rfl (fun _ _ e => by cases e) hl (.call rfl)
    apply RunsQ.chunk rfl (runs_getObjG ArenaField.funcs _ _ (by exact hf)) hl
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
    apply LRun.store_congrG (S' := iStore₁ S c tyU32) ((e₁ _ rfl).trans rfl)
    have hS₁ : (iStore₁ S c tyU32).insts = [ι] := hi
    apply RunsQ.chunk (th := some ⟨S.threads.length⟩)
      (p := Task.enterImplicitThread Quirks.none ⟨S.tasks.length⟩) (a := true) rfl
      (runs_enterG' (Gt := S.tasks) (y := callTask S tyU32) rfl rfl rfl hS₁ hadd) hl
    have e₂ : CStore.registerThreadSt ⟨S.tasks.length⟩ ⟨S.threads.length⟩
        (CStore.setImplicitThread ⟨S.tasks.length⟩ ⟨S.threads.length⟩ (iStore₁ S c tyU32)) =
          iStore₂ S c tyU32 ι' :=
      registerThreadSt_eqG (tasks_modify_lastG rfl _) rfl hS₁ hadd rfl
    apply LRun.store_congrG (S' := iStore₂ S c tyU32 ι') (by exact e₂)
    have hS₂ : (iStore₂ S c tyU32 ι').tasks =
        S.tasks ++ [callTask₁ S tyU32 ⟨S.threads.length⟩] := rfl
    have hcl : ArenaField.callers.get? (iStore₂ S c tyU32 ι')
        (callTask₁ S tyU32 ⟨S.threads.length⟩).caller = some (.host c [] 0) := by
      show (S.callers ++ [_])[S.callers.length]? = _
      rw [List.getElem?_concat_length]
    apply RunsQ.chunk rfl (runs_getObjG ArenaField.tasks _ _ (tasks_get_lastG (Gt := S.tasks) hS₂))
      hl
    apply RunsQ.chunk rfl (runs_startHG (Gt := S.tasks) hS₂ hcl) hl
    apply RunsQ.chunk rfl (runs_lower_nilU _ _) hl
    apply LRun.store_congrG (S' := iStore₃ S c tyU32 ι' S.core) (by
      exact setTaskState_lastG (Gt := S.tasks) (y := callTask₁ S tyU32 ⟨S.threads.length⟩)
        rfl _)
    mstepG
    exact .refl _
  refine ⟨rfl, rfl, hl, ?_⟩
  intro y v
  apply Exists.intro; apply Exists.intro
  refine ⟨?_, ?_⟩
  · apply LRun.store_congrG (S' := iStore₃ S c tyU32 ι' y.1) rfl
    have hS₃ : (iStore₃ S c tyU32 ι' y.1).tasks =
        S.tasks ++ [(callTask₁ S tyU32 ⟨S.threads.length⟩).withState .started] := rfl
    have hcl : ArenaField.callers.get? (iStore₃ S c tyU32 ι' y.1)
        ((callTask₁ S tyU32 ⟨S.threads.length⟩).withState .started).caller =
          some (.host c [] 0) := by
      show (S.callers ++ [_])[S.callers.length]? = _
      rw [List.getElem?_concat_length]
    unfold retCfg
    apply RunsQ.chunk2 rfl (runs_lift_u32G (impl := impl) _ _ v).choose_spec hl
    apply RunsQ.chunk2 rfl (runs_returnHG (Gt := S.tasks) _ hS₃ rfl rfl hcl) hl
    apply LRun.store_congrG (S' := iStore₄ S c tyU32 ι' y.1)
      (by refine setTaskState_lastG (Gt := S.tasks) ?_ _; rfl)
    apply RunsQ.chunk rfl
      (runs_exitG (impl := impl) (Gt := S.tasks) (Gth := S.threads)
        (y := ((callTask₁ S tyU32 ⟨S.threads.length⟩).withState .started).withState .resolved)
        (z := (startThread S.tasks).withIndex 1) (ι := ι') rfl rfl rfl rfl rfl rfl rfl rfl hrem) hl
    have e₄ : CStore.unregisterThreadSt ⟨S.tasks.length⟩ ⟨S.threads.length⟩ 1
        (iStore₄ S c tyU32 ι' y.1) =
          { iStore₄ S c tyU32 ι' y.1 with
            tasks := S.tasks ++ [callTaskEnd S tyU32 ⟨S.threads.length⟩]
            insts := [InstState.removeThread 1 ι'] } :=
      unregisterThreadSt_eqG _ _ rfl rfl rfl
    apply LRun.store_congrG (S' := { iStore₄ S c tyU32 ι' y.1 with
        tasks := S.tasks ++ [callTaskEnd S tyU32 ⟨S.threads.length⟩]
        insts := [InstState.removeThread 1 ι'] }) e₄
    mstepG
    have e₅ : threadStatusSt ⟨S.threads.length⟩ .exited
        { iStore₄ S c tyU32 ι' y.1 with
          tasks := S.tasks ++ [callTaskEnd S tyU32 ⟨S.threads.length⟩]
          insts := [InstState.removeThread 1 ι'] } = iStore₅ S c tyU32 ι' y.1 :=
      threadStatus_lastG (z := (startThread S.tasks).withIndex 1) rfl _
    apply LRun.store_congrG (S' := iStore₅ S c tyU32 ι' y.1) e₅
    apply RunsQ.chunk rfl (runs_callUnit_loopG (impl := impl) (Gt := S.tasks) rfl rfl) hl
    repeat mstepG
    exact .refl _
  · rw [hostFinish_cancelG _ pending c f [] _ rfl]
    exact ⟨rfl, hl, rfl, rfl⟩

end Call

/-! ## `Task.callLift` -/

section Ref

open Silmaril.Wasm.Component.DecoderBridge Silmaril.Wasm.Component.InstRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (neverFail)

/-- The reference type read as `func() -> u32` is `tyU32`. -/
theorem tyRel_getTy {ty : Types.FuncType RtId} (h : TyRel ty getTy) : ty = tyU32 := by
  obtain ⟨⟨as, ps, res⟩, fr, -, hr, ht⟩ := h
  cases as
  · cases ps with
    | cons p ps =>
      exfalso
      simp only [refFuncTy, Bool.false_eq_true, ↓reduceIte] at hr
      cases h1 : refVT p.2 <;> simp [h1] at hr
      cases h2 : ps.mapM (fun p => refVT p.2) <;> simp [h2] at hr
      rcases res with _ | t
      · repeat' split at hr
        all_goals simp_all [getTy]
      · cases h3 : refVT t <;> simp only [h3, Option.map_none, Option.map_some,
          Option.bind_none, Option.bind_some, reduceCtorEq] at hr
        repeat' split at hr
        all_goals simp_all [getTy]
    | nil =>
      rcases res with _ | (q | i)
      · simp [refFuncTy] at hr
      · cases q <;> first
          | (simp [refFuncTy, refVT, refPrim] at hr; done)
          | (simp only [Instantiate.resolveFuncType?, Instantiate.resolveOptValType?] at ht
             cases ht; rfl)
      · simp [refFuncTy, refVT] at hr
  · simp [refFuncTy] at hr

/-- `core3`'s internal step is only enabled at `running` threads: every engine run is a run the
machine allows. -/
theorem coreSteps_of_core3 {o : Silmaril.Wasm.SingleThreaded.GrowOracle} {x y : CoreSt (core3 o)}
    (h : Engine.CoreEngine.Steps (core3 o) x y) : Relation.ReflTransGen (CoreStep (core3 o)) x y := by
  induction h with
  | refl => exact .refl
  | @tail b c' _ hs ih =>
    refine ih.tail ⟨.inl ?_, hs⟩
    obtain ⟨s, t⟩ := b
    by_contra hn
    have e := Silmaril.Wasm.Component.Engine.Core3.statusE_not_running_no_step (o := o) hn
    have hs' : Silmaril.Wasm.SingleThreaded.internalC (Silmaril.Wasm.SingleThreaded.Exec.stepI o)
        (s, t) = some c' := hs
    rw [e] at hs'
    cases hs'

/-- **The session call through `canon lift`** (`Task.callLift`, with the host-readiness condition
`nestingDepth = 0` of the invoke). -/
theorem callLift_core3
    (M : Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent)) (f : FuncId) (a : Nat)
    (ty : Types.FuncType RtId) (y : (core3 neverFail).Config (CanonHost (core3 neverFail)))
    (v : BitVec 32)
    (hc : M.ctl = []) (hl : M.store.lockdown = false) (hd : M.store.nestingDepth = 0)
    (hι : ∃ ι, M.store.insts = [ι] ∧ InstOk ι) (hp : M.pending = []) (hres : M.results = [])
    (hf : ArenaField.funcs.get? M.store f = some (.lifted a ty {} ⟨0⟩)) (hty : TyRel ty getTy)
    (hrun : Engine.CoreEngine.Steps (core3 neverFail) (M.store.core, (core3 neverFail).invoke a []) y)
    (hst : (core3 neverFail).status y.1 y.2 = .returned (.values [⟨.int .i32, v⟩])) :
    ∃ M', LinkedSession.SessRun first.prof (Host.ofEmbedder embL) M 0 [(f, [])]
      [some [toRefVal (.u32 v)]] M' ∧ M'.host = M.host := by
  obtain rfl := tyRel_getTy hty
  obtain ⟨ι, hi, hok⟩ := hι
  obtain ⟨ι', hadd, hrem, -, -⟩ := inst_round hok ⟨M.store.threads.length⟩
  obtain ⟨M₀, thc, Kc, segsc, restc, tr₁, h₁, hctl, hcore, hl₀, hret⟩ :=
    invoke_atG (impl := embL.host) first.prof M ⟨0⟩ f a ι ι' hl hi hf hadd hrem
  obtain ⟨tr₂, M', h₂, hc', hl', hh', hr'⟩ := hret y v
  have hM₀ : M₀ = coreCfg M₀ thc Kc segsc restc (M.store.core, (core3 neverFail).invoke a []) := by
    obtain ⟨S₀, h₀, ctl₀, conts, pending, results, cancels⟩ := M₀
    dsimp only at hctl hcore ⊢
    subst hctl
    unfold coreCfg
    rw [← hcore]
  obtain ⟨trc, htrc, hcs⟩ := Adequacy.coreCfg_steps_of (prof := first.prof) (hr := fun _ _ => false)
    (dispatch := DG embL.host) (B := M₀) (th := thc) (K := Kc) (segs := segsc) (rest := restc)
    (coreSteps_of_core3 hrun)
  have hretS : Step first.prof (fun _ _ => false) (DG embL.host)
      (coreCfg M₀ thc Kc segsc restc y) .tau (retCfg M₀ thc Kc segsc restc y [⟨.int .i32, v⟩]) :=
    Step.coreReturned rfl hst
  have hinv : Step first.prof (fun _ _ => false) (DG embL.host) M
      (.host (invokeTop ⟨0⟩ f [])) (invokedG M ⟨0⟩ f) :=
    Step.hostInvoke ⟨hc, hl, hd⟩ (by rw [hp]; intro x hx; cases hx)
  have hsteps := Adequacy.steps_append h₁.steps (by
    rw [← hM₀] at hcs
    exact Adequacy.steps_append hcs (.cons hretS h₂.steps))
  refine ⟨M', .ret ⟨_, .cons hinv hsteps, ?_, ?_⟩ (.nil _ _), hh'⟩
  · intro ev hm
    rcases List.mem_append.mp hm with hm | hm
    · exact absurd hm (Adequacy.LRun.no_host h₁ ev)
    rcases List.mem_append.mp hm with hm | hm
    · cases htrc _ hm
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
    · exact absurd hm (Adequacy.LRun.no_host h₂ ev)
  refine ⟨?_, ?_⟩
  · intro e
    cases e
  have hr0 : M'.result? ⟨0⟩ = some (some [toRefVal (.u32 v)]) := by
    show (M'.results.find? (·.1 == ⟨0⟩)).map Prod.snd = _
    rw [hr', hres]
    rfl
  exact ⟨hc', hl', hr0⟩

/-- **`Task.callLift`.** -/
theorem callLift : Task.callLift := by
  intro M f a ty y v hc hl hd hι hp hres _ _ hf hty hrun hst
  exact callLift_core3 M f a ty y v hc hl hd hι hp hres hf hty hrun hst

end Ref

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
