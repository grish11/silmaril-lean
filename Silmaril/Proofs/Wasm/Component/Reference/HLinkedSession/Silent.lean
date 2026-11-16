module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.TrapS
public import Silmaril.Wasm.Component.Reference.HLinkedSession.Defs

/-!
# A `canon lower` callout to a host that never answers

A core activation of the reference machine stopped at `.callout h args`, with `h` the
synchronous `canon lower` trampoline `.lowered f ft {} inst` of a host function `f`, under the
host `HLinked2.silentHost` (`silentImpl`: `on_start`, then return without resolving):

* `BlocksQ`: the big-step form of a program that reaches `block()`; `BlocksQ.lrun` places it in
  any context as a live run, and `BlocksQ.steps_block` takes the `block` step, which saves the
  activation and returns to the resumer (`Step.block`);
* `blocks_callout_silent`: when the arguments lift, the callout program runs `canonLower`: the
  entry check, a fresh subtask and caller record, the host function (`on_start` lifts the
  arguments and marks the subtask `STARTED`), and then, the subtask unresolved, the synchronous
  `wait_until(subtask.resolved)` (REF `canon_lower`, L2213), which starts waiting on
  `subtaskResolved` and blocks. The store is then `silentSt`.

The trap that follows in the synchronous lift loop (`cannotBlockSync`) is
`LinkedSessionFwd.CallAtLKTS.block`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

/-! ## Big-step runs to a block -/

section Generic

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

variable (dispatch) in
/-- **Big-step runs to a block**: the program `p` on thread `th` runs from `m` to a
configuration whose program in focus is `block()` (no thread to switch to), possibly inside
late-bound calls. -/
inductive BlocksQ : {α : Type} → Option ThreadId → Canon.P E σ α → Config E σ →
    List (Label E σ) → Config E σ → Prop where
  | block {α : Type} {th : Option ThreadId} {k : Unit → Canon.P E σ α} (m : Config E σ) :
      BlocksQ th (.op (S := Eff E σ) (.block none) k) m [] m
  | bind {α β : Type} {th : Option ThreadId} {p : Canon.P E σ α} {f : α → Canon.P E σ β}
      {m m₁ mB : Config E σ} {tr₁ tr₂ : List (Label E σ)} {a : α} :
      RunsQ dispatch th p m tr₁ a m₁ → BlocksQ th (f a) m₁ tr₂ mB →
      BlocksQ th (p >>= f) m (tr₁ ++ tr₂) mB
  | left {α β : Type} {th : Option ThreadId} {p : Canon.P E σ α} {f : α → Canon.P E σ β}
      {m mB : Config E σ} {tr : List (Label E σ)} :
      BlocksQ th p m tr mB → BlocksQ th (p >>= f) m tr mB
  | callIn {α : Type} {th : Option ThreadId} {c : Call E} {k : Ret E → Canon.P E σ α}
      {m mB : Config E σ} {tr : List (Label E σ)} :
      BlocksQ th (dispatch c) m tr mB → BlocksQ th (callRet c >>= k) m (.tau :: tr) mB

namespace BlocksQ

theorem lock {α : Type} {th : Option ThreadId} {p : Canon.P E σ α} {m mB : Config E σ}
    {tr : List (Label E σ)} (h : BlocksQ dispatch th p m tr mB) :
    mB.store.lockdown = m.store.lockdown := by
  induction h with
  | block => rfl
  | bind h₁ _ ih => exact ih.trans h₁.lock
  | left _ ih => exact ih
  | callIn _ ih => exact ih

/-- **A big-step run to a block is a live run to the block**, in any context. -/
theorem lrun {α : Type} {th : Option ThreadId} {p : Canon.P E σ α} {m mB : Config E σ}
    {tr : List (Label E σ)} (h : BlocksQ dispatch th p m tr mB) :
    m.store.lockdown = false →
    ∀ (f : α → Canon.P E σ (Ret E)) (segs : List (Seg E σ)) (rest : List (Activation E σ)),
      ∃ (k : Unit → Canon.P E σ (Ret E)) (segs' : List (Seg E σ)),
        LRun prof hr dispatch { m with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } tr
          { mB with ctl := ⟨th, .prog (.op (S := Eff E σ) (.block none) k), segs'⟩ :: rest } := by
  induction h with
  | @block _ th k m =>
    intro _ f segs rest
    exact ⟨fun u => k u >>= f, segs, .refl _⟩
  | @bind _ _ th p f₀ m m₁ mB tr₁ tr₂ a h₁ _ ih =>
    intro hl f segs rest
    have hl₁ : m₁.store.lockdown = false := h₁.lock.trans hl
    obtain ⟨k, segs', hrun⟩ := ih hl₁ f segs rest
    have d₁ := h₁.lrun (prof := prof) (hr := hr) hl (fun a => f₀ a >>= f) segs rest
    have e : (p >>= f₀) >>= f = p >>= fun a => f₀ a >>= f := by
      rw [Prog.bind_eq, Prog.bind_eq, Prog.bind_assoc]
      rfl
    rw [e]
    exact ⟨k, segs', d₁.trans hrun⟩
  | @left _ _ th p f₀ m mB tr _ ih =>
    intro hl f segs rest
    have e : (p >>= f₀) >>= f = p >>= fun a => f₀ a >>= f := by
      rw [Prog.bind_eq, Prog.bind_eq, Prog.bind_assoc]
      rfl
    rw [e]
    exact ih hl (fun a => f₀ a >>= f) segs rest
  | @callIn _ th c k m mB tr _ ih =>
    intro hl f segs rest
    obtain ⟨k', segs', hrun⟩ := ih hl Prog.pure (.prog (fun r => k r >>= f) :: segs) rest
    have s₁ : UniqueStep prof hr dispatch
        { m with ctl := ⟨th, .prog (.op (S := Eff E σ) (.call c) fun r => k r >>= f), segs⟩ ::
          rest }
        .tau { m with ctl := ⟨th, .prog (dispatch c), .prog (fun r => k r >>= f) :: segs⟩ ::
          rest } :=
      .of_prog rfl (fun _ _ e => by cases e) (.call (k := fun r => k r >>= f) rfl)
    rw [Prog.bind_eq, Prog.bind_pure] at hrun
    exact ⟨k', segs', .cons (RunsQ.live_op hl) s₁ hrun⟩

/-- **A big-step run to a block, then the block**: the activation is saved, the thread marked
blocked, and control returns to the resumer `rest`. -/
theorem steps_block {α : Type} {t : ThreadId} {p : Canon.P E σ α} {m mB : Config E σ}
    {tr : List (Label E σ)} (h : BlocksQ dispatch (some t) p m tr mB)
    (hl : m.store.lockdown = false) (f : α → Canon.P E σ (Ret E)) (segs : List (Seg E σ))
    (rest : List (Activation E σ)) :
    ∃ (k : Unit → Canon.P E σ (Ret E)) (segs' : List (Seg E σ)),
      Steps prof hr dispatch { m with ctl := ⟨some t, .prog (p >>= f), segs⟩ :: rest }
        (tr ++ [.tau])
        { (mB.setCont t (some (blockedAct t k segs'))) with
          store := threadStatusSt t .blocked mB.store, ctl := rest } := by
  obtain ⟨k, segs', hrun⟩ := h.lrun (prof := prof) (hr := hr) hl f segs rest
  exact ⟨k, segs', Adequacy.steps_append hrun.steps (.cons (Step.block rfl) (.refl _))⟩

end BlocksQ

theorem runsQ_pure_eq {α : Type} {th : Option ThreadId} {a b : α} {m : Config E σ}
    (h : a = b) : RunsQ dispatch th (.pure a) m [] b m :=
  h ▸ .pure a m

end Generic

/-! ## The silent callout -/

section Silent

variable {P : Profile} {σ : Type}

/-- `on_start` dispatched to a `canon_lower` caller record, under any host functions. -/
theorem runs_onStartLowerI {impl : HostImpl (E3 P) σ} {th : Option ThreadId}
    {m m' : Machine.Config (E3 P) σ} {c : CallerId} {x : Caller (E3 P)}
    {tr : List (Label (E3 P) σ)} {vs : List Silmaril.Wasm.Component.Reference.Val}
    (hc : ArenaField.callers.get? m.store c = some x)
    (hx : ∀ S cx ys pos ft mp mr, x = .lower S cx ys pos ft mp mr →
      RunsQ (DI P impl) th (lowerOnStart Limits.spec Quirks.none c) m tr vs m')
    (hl : ∃ S cx ys pos ft mp mr, x = .lower S cx ys pos ft mp mr) :
    RunsQ (DI P impl) th (DI P impl (.onStart c)) m (.tau :: (tr ++ [])) (.vals vs) m' := by
  obtain ⟨S, cx, ys, pos, ft, mp, mr, rfl⟩ := hl
  exact RunsQ.getObj_bind _ _ hc (RunsQ.bind (hx _ _ _ _ _ _ _ rfl) (RunsQ.pure _ _))

/-- **The silent host function, called through a `canon_lower` caller record**, lifts the
arguments (`on_start`) and returns without resolving the subtask. -/
theorem runs_silentFn {th : Option ThreadId} {m : Machine.Config (E3 P) σ} {fn : HostFuncId}
    {c : CallerId} {S : SubtaskId} {cx : LiftLowerContext (E3 P)} {ys : List Flat}
    {p : Silmaril.Wasm.Component.FuncTy} {xS : Subtask} {ws : List Silmaril.Wasm.Component.Val}
    (hc : ArenaField.callers.get? m.store c = some (.lower S cx ys 0 (witFt p) 16 1))
    (hS : ArenaField.subtasks.get? m.store S = some xS) (hidx : xS.index = none)
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws) :
    ∃ pos tr, RunsQ (DI P HLinked2.silentImpl) th
      ((HLinked2.silentImpl : HostImpl (E3 P) σ).funcs fn c) m tr (.cancel .none)
      { m with store := LowerSt.setCallerPosSt c pos (LowerSt.startSt S m.store) } := by
  obtain ⟨pos, tr₁, h₁⟩ := runs_lowerOnStart (d := DI P HLinked2.silentImpl) (th := th) hc hS
    hidx hpf hys hmaxp hws
  refine ⟨pos, ?_⟩
  apply Exists.intro
  apply RunsQ.call_bind (runs_onStartLowerI hc (fun _ _ _ _ _ _ _ _ => h₁)
    ⟨_, _, _, _, _, _, _, rfl⟩)
  exact RunsQ.pure _ _

/-- The store once a silent callout blocks: the callout's subtask (started, unresolved) and
`canon_lower` caller record, the thread `t` waiting on the subtask's resolution. -/
def silentSt (s : CStore (E3 P)) (inst : InstId) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) (pos : Nat) (t : ThreadId) : CStore (E3 P) :=
  CStore.startWaitingSt t (.subtaskResolved ⟨s.subtasks.length⟩)
    (LowerSt.setOnCancelSt ⟨s.subtasks.length⟩ .none
      (LowerSt.setCallerPosSt ⟨s.callers.length⟩ pos
        (LowerSt.startSt ⟨s.subtasks.length⟩ (allocSC s inst ys p))))

/-- The subtask of a silent callout is not resolved. -/
theorem silent_unresolved (s : CStore (E3 P)) (inst : InstId) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) (pos : Nat) :
    (LowerSt.setOnCancelSt ⟨s.subtasks.length⟩ CancelRef.none
      (LowerSt.setCallerPosSt ⟨s.callers.length⟩ pos
        (LowerSt.startSt ⟨s.subtasks.length⟩ (allocSC s inst ys p)))).subtaskResolved
      ⟨s.subtasks.length⟩ = false := by
  simp [CStore.subtaskResolved, CStore.subtask?, LowerSt.setOnCancelSt, LowerSt.setCallerPosSt,
    LowerSt.startSt, ArenaField.get?_modify, allocSC_subtasks, AsyncRef.SubtaskState.resolved]

/-- **`wait_until` on an unresolved subtask** starts waiting and blocks. -/
theorem blocks_wait {impl : HostImpl (E3 P) σ} {t : ThreadId} {m : Machine.Config (E3 P) σ}
    {S : SubtaskId} (hS : m.store.subtaskResolved S = false) :
    BlocksQ (DI P impl) (some t) (Thread.waitUntilGuest .syncLower (.subtaskResolved S)) m
      [.tau, .tau, .tau] { m with store := CStore.startWaitingSt t (.subtaskResolved S) m.store } := by
  unfold Thread.waitUntilGuest Thread.waitUntil
  refine BlocksQ.bind (tr₁ := [.tau]) (tr₂ := [.tau, .tau])
    (RunsQ.currentThread (RunsQ.pure _ _)) ?_
  refine BlocksQ.bind (tr₁ := [.tau]) (tr₂ := [.tau]) (a := false)
    (RunsQ.get (runsQ_pure_eq hS)) ?_
  refine BlocksQ.bind (tr₁ := []) (tr₂ := [.tau]) (RunsQ.pure _ _) ?_
  refine BlocksQ.bind (tr₁ := [.tau]) (tr₂ := []) (RunsQ.modify rfl (RunsQ.pure _ _)) ?_
  exact BlocksQ.block _

/-- **`canonLower` of a host function under the silent host blocks.** -/
theorem blocks_canonLower_silent {t : ThreadId} {m : Machine.Config (E3 P) σ} {f : FuncId}
    {ft' : WIT.FuncType Empty RtId} {fn : HostFuncId} {inst : InstId} {st : InstState}
    {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy} {ws : List Silmaril.Wasm.Component.Val}
    (hi : ArenaField.insts.get? m.store inst = some st) (hleave : st.mayLeave = true)
    (hf : ArenaField.funcs.get? m.store f = some (.host ft' fn))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws) :
    ∃ pos tr, BlocksQ (DI P HLinked2.silentImpl) (some t)
      (canonLower Limits.spec Quirks.none f (witFt p) {} inst ys) m tr
      { m with store := silentSt m.store inst ys p pos t } := by
  have hf₂ : ArenaField.funcs.get? (allocSC m.store inst ys p) f = some (.host ft' fn) := hf
  obtain ⟨pos, tr₁, h₁⟩ := runs_silentFn (th := some t) (fn := fn)
    (m := { m with store := allocSC m.store inst ys p }) (allocSC_callers _ _ _ _)
    (allocSC_subtasks _ _ _ _) rfl hpf hys hmaxp hws
  have hfi : RunsQ (DI P HLinked2.silentImpl) (some t)
      (DI P HLinked2.silentImpl (.funcInst f ⟨m.store.callers.length⟩))
      { m with store := allocSC m.store inst ys p } (.tau :: tr₁) (.cancel .none)
      { m with store := (LowerSt.setCallerPosSt ⟨m.store.callers.length⟩ pos
          (LowerSt.startSt ⟨m.store.subtasks.length⟩ (allocSC m.store inst ys p))) } :=
    RunsQ.getObj_bind _ _ hf₂ h₁
  have hres := silent_unresolved m.store inst ys p pos
  refine ⟨pos, ?_⟩
  apply Exists.intro
  apply BlocksQ.bind (runs_getObj ArenaField.insts _ _ hi)
  rw [hleave]
  apply BlocksQ.bind (RunsQ.pure _ _)
  apply BlocksQ.bind (runsQ_allocObj _ _ rfl)
  apply BlocksQ.bind (runsQ_allocObj _ _ rfl)
  apply BlocksQ.bind (RunsQ.call_bind hfi (RunsQ.pure _ _))
  apply BlocksQ.bind (RunsQ.modify rfl (RunsQ.pure _ _))
  apply BlocksQ.bind (a := false) (RunsQ.get (runsQ_pure_eq hres))
  exact BlocksQ.left (blocks_wait hres)

/-- **A callout to a host function under the silent host blocks**: from the entry check to the
synchronous `wait_until` of `canonLower`, at the store `silentSt`. -/
theorem blocks_callout_silent {t : ThreadId} {m : Machine.Config (E3 P) σ} {f : FuncId}
    {ft' : WIT.FuncType Empty RtId} {fn : HostFuncId} {inst : InstId} {st : InstState}
    {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy} {ws : List Silmaril.Wasm.Component.Val}
    (hentry : calloutEntry m.store (some t) (.lowered f (witFt p) {} inst) = none)
    (hi : ArenaField.insts.get? m.store inst = some st) (hleave : st.mayLeave = true)
    (hf : ArenaField.funcs.get? m.store f = some (.host ft' fn))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws) :
    ∃ pos tr, BlocksQ (DI P HLinked2.silentImpl) (some t)
      (DI P HLinked2.silentImpl (.hostCallout (.lowered f (witFt p) {} inst) ys)) m tr
      { m with store := silentSt m.store inst ys p pos t } := by
  obtain ⟨pos, tr, h⟩ := blocks_canonLower_silent (t := t) hi hleave hf hpf hys hmaxp hws
  refine ⟨pos, ?_⟩
  apply Exists.intro
  apply BlocksQ.bind (RunsQ.currentThread (RunsQ.pure _ _))
  apply BlocksQ.bind (RunsQ.get (RunsQ.pure _ _))
  show BlocksQ _ _ (match calloutEntry m.store (some t) (.lowered f (witFt p) {} inst) with
    | some r => trap r | none => _) _ _ _
  rw [hentry]
  exact BlocksQ.left h

end Silent

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
