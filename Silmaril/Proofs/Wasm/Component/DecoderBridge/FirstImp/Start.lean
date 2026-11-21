module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.HostCode
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Main

/-!
# A start run with host calls, in the reference machine

The IR runs the start function of a module whose imports are the lowerings of
`f: func(u32)` against fresh host functions (`StartRunI`): runs of internal steps separated by
import calls, each answered (here: with no results, `.flat []`) and resumed. The reference machine
runs the same code in the core store with the host code renamed to the trampoline `lowH`
(`Store.mapH gL`), under the logging host `embL`:

* `seg_ref`: an internal run of the IR to an import call is matched by a live run of the machine
  that runs the core activation to the callout (`runCI_complete` along typing, `lrun_runC`),
  calls `f` through `canon lower` (`hostCall_lrunX`: the logging host answers `()` and logs the
  call) and resumes the activation with no results: the thread is the IR's resumed thread, the
  host log grows by one event, the call of `f` on the `u32` argument of the callout;
* `startRun_ref`: so a whole start run of the IR, ending at a returned status (values or trap),
  is matched by a live run of the machine to the core activation at the same returned status,
  with the host log extended by `coreLog ys`, one event per import call of the IR.

The invariants: `RT` (the core store and thread are typed, and every host function of the store
has core type `fFlat`) and `CallInv` (the store is unlocked, the current thread belongs to the
root instance `0`, which may leave, and component function `0` is the host function `f`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.SingleThreaded (GrowOracle Internal status statusC runC neverFail profile)
open Silmaril.Wasm.SingleThreaded.Exec (stepI)
open Silmaril.Wasm.Execution.Core (Store FuncInst StoreOk ConfigOk)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "Σh" => Unit × List HLinked2.HostEvent

/-! ## Threads up to their configuration -/

section Congr

variable {H : Type} {o : GrowOracle}

theorem internal_congr {s : Store H} {t t' : STh} (h : t.config s = t'.config s)
    (y : Store H × STh) : Internal o (s, t) y ↔ Internal o (s, t') y := by
  rcases y with ⟨s', t''⟩
  show (∃ f' code', _ ∧ Silmaril.Wasm.Execution.Core.Step _ _ (t.config s) _) ↔
    (∃ f' code', _ ∧ Silmaril.Wasm.Execution.Core.Step _ _ (t'.config s) _)
  rw [h]

theorem status_congr {s : Store H} {t t' : STh} (h : t.config s = t'.config s) :
    status o s t = status o s t' := by
  have e : ∀ y, Internal o (s, t) y = Internal o (s, t') y :=
    fun y => propext (internal_congr h y)
  unfold status
  rw [h]
  split_ifs <;> first | rfl | (exfalso; simp_all)

theorem resume_congr {s : Store H} {t t' : STh} (h : t.config s = t'.config s)
    {x : Silmaril.Wasm.SingleThreaded.Ctx × Nat × H × List Silmaril.Wasm.Execution.Core.Val}
    (hd : Silmaril.Wasm.SingleThreaded.decompose? s (t.config s).code = some x)
    (r : Silmaril.Wasm.SingleThreaded.CallResult) :
    Silmaril.Wasm.SingleThreaded.resume s t r = Silmaril.Wasm.SingleThreaded.resume s t' r := by
  unfold Silmaril.Wasm.SingleThreaded.resume
  dsimp only
  rw [← h, hd]

end Congr

/-! ## The invariants -/

/-- The renaming of the IR's host code to the trampoline of `f`. -/
abbrev gL : Nat → CanonHost (core3 neverFail) := fun _ => lowH

/-- Every host function of the store has core type `fFlat`. -/
def HostTy {H : Type} (S : Store H) : Prop :=
  ∀ fi ∈ S.funcs, ∀ h, fi.code = .host h →
    fi.type = Silmaril.Wasm.SingleThreaded.ofFlatType (Param.v1Type fFlat)

/-- The core store and thread of the machine are typed, with host functions of type `fFlat`. -/
structure RT (S : Store (CanonHost (core3 neverFail))) (t : STh) : Prop where
  store : StoreOk S
  thread : Silmaril.Wasm.SingleThreaded.ThreadOk S t []
  hosts : HostTy S

/-- The machine around the core activation of the start function. -/
structure CallInv {σ : Type} (B : Machine.Config (core3 neverFail) σ) (th : Option ThreadId) :
    Prop where
  lock : B.store.lockdown = false
  entry : calloutEntry B.store th lowH = none
  inst : ∃ st, ArenaField.insts.get? B.store ⟨0⟩ = some st ∧ st.mayLeave = true
  func : ArenaField.funcs.get? B.store ⟨0⟩ = some (.host fWit ⟨0⟩)

/-- The host event of an import call of the IR's start run with one `i32` argument: the call of
`f` on it, answered `()`. -/
def coreEvent {n : Nat} (y : Σ _ : (sigN n).Op, Option Payload) : Option HLinked2.HostEvent :=
  match y.1.2 with
  | .flat [⟨.int .i32, b⟩] => some (⟨0⟩, [toRefVal (.u32 b)], [])
  | _ => none

/-- The host log of the IR's import calls. -/
def coreLog {n : Nat} (ys : List (Σ _ : (sigN n).Op, Option Payload)) :
    List HLinked2.HostEvent :=
  ys.filterMap coreEvent

/-! ## Callouts of typed threads -/

theorem args_of_callout {S : Store (CanonHost (core3 neverFail))} {t : STh} (hR : RT S t)
    {h : CanonHost (core3 neverFail)} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hst : status neverFail S t = .callout h args) :
    ∃ b : BitVec 32, args = [.num ⟨.int .i32, b⟩] := by
  obtain ⟨fi, hfi, hcode, ps, rs, hexp, hargs⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.callout_args_typed hR.store hR.thread hst
  have hty := hR.hosts fi hfi h hcode
  rw [hty] at hexp
  have he := Silmaril.Wasm.Execution.Core.Expand.func_eq hexp
    (Silmaril.Wasm.Component.Engine.Core3.Typed.expand_ofFlatType (Param.v1Type fFlat))
  injection he with he₁ he₂
  rw [he₁] at hargs
  simp only [Param.v1Type, fFlat, List.map_cons, List.map_nil,
    Silmaril.Wasm.Validation.Ty.toList_ofList] at hargs
  rcases hargs with _ | ⟨hv, hrest⟩
  cases hrest
  obtain ⟨b, rfl⟩ := Silmaril.Wasm.Execution.Core.ValOk.int_inv hv
  exact ⟨b, rfl⟩

/-- Resuming a typed thread at a callout with no results gives a typed thread. -/
theorem rt_resume {S : Store (CanonHost (core3 neverFail))} {t : STh} (hR : RT S t)
    {h : CanonHost (core3 neverFail)} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hst : status neverFail S t = .callout h args) :
    RT S (Silmaril.Wasm.SingleThreaded.resume S t (.values [])) := by
  refine ⟨hR.store, ?_, hR.hosts⟩
  refine Silmaril.Wasm.SingleThreaded.resume_typed hR.store hR.thread hst hR.store
    (Silmaril.Wasm.Execution.Core.Extend.refl hR.store) ?_
  intro E a args' hd
  obtain ⟨fi, yy, ps, rs, hfi, hcode, -, he, -, -⟩ :=
    Silmaril.Wasm.SingleThreaded.decompose?_sound hd
  have hty := hR.hosts fi (List.mem_of_getElem? hfi) h hcode
  refine ⟨fi, _, _, hfi, by
    rw [hty]
    exact Silmaril.Wasm.Component.Engine.Core3.Typed.expand_ofFlatType (Param.v1Type fFlat), ?_⟩
  simp [Param.v1Type, fFlat]


/-! ## Statuses of the concrete engine -/

theorem statusE_flat {H : Type} (o : GrowOracle) (S : Store H) (t : STh) :
    Silmaril.Wasm.Component.Engine.Core3.statusE o S t = flatStatus (statusC (stepI o) S t) := by
  unfold Silmaril.Wasm.Component.Engine.Core3.statusE flatStatus
  rcases statusC (stepI o) S t with _ | ⟨_ | _⟩ | _ | _ <;> rfl

theorem flatStatus_returned {H : Type} {st : Silmaril.Wasm.SingleThreaded.Status H}
    {r : Engine.CallResult} (h : flatStatus st = .returned r) :
    ∃ r', st = .returned r' := by
  rcases st with _ | ⟨_ | _⟩ | _ | _ <;> simp only [flatStatus] at h
  · cases h
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · split at h <;> cases h
  · cases h

theorem funcs_stepsG {H : Type} {o : GrowOracle} {x y : Store H × STh}
    (h : Relation.ReflTransGen (Internal o) x y) : y.1.funcs = x.1.funcs := by
  induction h with
  | refl => rfl
  | @tail b c _ hst ih =>
    obtain ⟨s, t⟩ := b
    obtain ⟨s', t'⟩ := c
    exact (Silmaril.Wasm.SingleThreaded.Internal.funcs_prefix hst).trans ih

/-! ## Segments of the start run -/

section Seg

variable {prof : ProfileKind} {th : Option ThreadId}
  {K : List Flat → Canon.P (core3 neverFail) Σh (Ret (core3 neverFail))}
  {segs : List (Seg (core3 neverFail) Σh)} {rest : List (Activation (core3 neverFail) Σh)}

/-- **An internal run of the IR, in the machine**: the core activation runs to the renamed end
of the run, typed. -/
theorem run_ref {B : Machine.Config (core3 neverFail) Σh} (hl : B.store.lockdown = false)
    {s s₁ : Store Nat} {t t₁ tR : STh}
    (hrun : Relation.ReflTransGen (Internal neverFail) (s, t) (s₁, t₁))
    (hth : tR.config (Store.mapH gL s) = t.config (Store.mapH gL s))
    (hR : RT (Store.mapH gL s) tR)
    (hst : status neverFail (Store.mapH gL s₁) t₁ ≠ .running) :
    ∃ tR' tr, LRun prof (fun _ _ => false) (DG embL.host)
        (coreCfg B th K segs rest (Store.mapH gL s, tR)) tr
        (coreCfg B th K segs rest (Store.mapH gL s₁, tR')) ∧ traceObs tr = [] ∧
      tR'.config (Store.mapH gL s₁) = t₁.config (Store.mapH gL s₁) ∧
      RT (Store.mapH gL s₁) tR' ∧
      statusC (stepI neverFail) (Store.mapH gL s₁) tR' =
        status neverFail (Store.mapH gL s₁) t₁ := by
  have h₁ := steps_of_internal hrun
  have h₂ := Steps.mapH (P := profile neverFail) gL h₁
  have h₃ : Relation.ReflTransGen
      (Silmaril.Wasm.Execution.Core.Step (profile neverFail) (fun _ _ _ _ => False))
      (tR.config (Store.mapH gL s)) (Config.mapH gL (t₁.config s₁)) := by
    rw [hth, config_mapHG]
    exact h₂
  obtain ⟨t', hr, ht'⟩ := internal_of_steps h₃
  have hd : (Config.mapH gL (t₁.config s₁)).store = Store.mapH gL s₁ := by
    show Store.mapH gL (t₁.config s₁).store = _
    rw [Silmaril.Wasm.SingleThreaded.Thread.config_store]
  rw [hd] at hr ht'
  have hth' : t'.config (Store.mapH gL s₁) = t₁.config (Store.mapH gL s₁) := by
    rw [ht', config_mapHG]
  obtain ⟨hs₁, ht₁⟩ := Silmaril.Wasm.SingleThreaded.reachable_typed hr hR.store hR.thread
  have hfun := funcs_stepsG hr
  have hR' : RT (Store.mapH gL s₁) t' := ⟨hs₁, ht₁, fun fi hfi => hR.hosts fi (by
    simp only at hfun; rw [← hfun]; exact hfi)⟩
  have hst' : status neverFail (Store.mapH gL s₁) t' = status neverFail (Store.mapH gL s₁) t₁ :=
    status_congr hth'
  obtain ⟨n, hn⟩ := runCI_complete (I := fun c => ConfigOk c [])
    Silmaril.Wasm.SingleThreaded.Exec.typedInv' hR.thread hr (by rw [hst']; exact hst)
  obtain ⟨tr, d, hob⟩ := lrun_runC (prof := prof) (hr := fun _ _ => false) (dispatch := DG embL.host)
    (k := K) (segs := segs) (rest := rest) (th := th) n hn
    (coreCfg B th K segs rest (Store.mapH gL s, tR)) rfl rfl hl
  refine ⟨t', tr, d, hob, hth', hR', ?_⟩
  rw [Silmaril.Wasm.SingleThreaded.Exec.statusI_eq_typed hR'.thread, hst']

/-- The lowering of `f: func(u32)`, as an IR function type. -/
abbrev fTy : Silmaril.Wasm.Component.FuncTy := ⟨[.u32], []⟩

theorem fWit_params : fWit.params.map (·.2) = toClosedList fTy.params := by decide +kernel

theorem fWit_result : fWit.result.toList = toClosedList fTy.results := by decide +kernel

/-- **An import call of the IR's start run, in the machine**: the core activation runs to the
callout of the trampoline, the logging host answers `()` to the call of `f` and logs it, and the
activation resumes with the IR's resumed thread. -/
theorem call_ref {B : Machine.Config (core3 neverFail) Σh} (hB : CallInv B th)
    {s s₁ : Store Nat} {t t₁ tR : STh}
    (hrun : Relation.ReflTransGen (Internal neverFail) (s, t) (s₁, t₁))
    (hth : tR.config (Store.mapH gL s) = t.config (Store.mapH gL s))
    (hR : RT (Store.mapH gL s) tR) {h : Nat} {args : List Flat}
    (hco : (core3P (profile neverFail)).status s₁ t₁ = .callout h args) :
    ∃ b : BitVec 32, args = [⟨.int .i32, b⟩] ∧
      ∃ (tr : List (Label (core3 neverFail) Σh)) (B' : Machine.Config (core3 neverFail) Σh),
        LRun prof (fun _ _ => false) (DG embL.host)
          (coreCfg B th K segs rest (Store.mapH gL s, tR)) tr
          (coreCfg B' th K segs rest
            (Store.mapH gL s₁, Silmaril.Wasm.SingleThreaded.resume s₁ t₁ (.values []))) ∧
        CallInv B' th ∧ B'.host = (B.host.1, B.host.2 ++ [(⟨0⟩, [toRefVal (.u32 b)], [])]) ∧
        RT (Store.mapH gL s₁) (Silmaril.Wasm.SingleThreaded.resume s₁ t₁ (.values [])) := by
  obtain ⟨args', hst', hfl⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.flatStatus_eq_callout' hco
  have hs₁ : status neverFail s₁ t₁ = .callout h args' := (statusP_profile s₁ t₁).symm.trans hst'
  have hsm : status neverFail (Store.mapH gL s₁) t₁ = .callout lowH args' :=
    status_mapH_callout hs₁
  obtain ⟨tR', tr₁, d₁, -, hth', hR', hC⟩ := run_ref (th := th) (K := K) (segs := segs)
    (rest := rest) (prof := prof) hB.lock hrun hth hR (by rw [hsm]; nofun)
  have hsR : status neverFail (Store.mapH gL s₁) tR' = .callout lowH args' :=
    (status_congr hth').trans hsm
  obtain ⟨b, rfl⟩ := args_of_callout hR' hsR
  simp only [List.mapM_cons, List.mapM_nil, Silmaril.Wasm.SingleThreaded.toFlat?] at hfl
  cases hfl
  have hE : (core3 neverFail).status (Store.mapH gL s₁) tR' = .callout lowH [⟨.int .i32, b⟩] := by
    have e := statusE_flat neverFail (Store.mapH gL s₁) tR'
    rw [hC, hsm] at e
    exact e
  obtain ⟨st, hi, hleave⟩ := hB.inst
  have hdec : ∃ x, Silmaril.Wasm.SingleThreaded.decompose? (Store.mapH gL s₁)
      (tR'.config (Store.mapH gL s₁)).code = some x := by
    obtain ⟨E, a, hd⟩ := Silmaril.Wasm.SingleThreaded.status_callout_inv hsR
    exact ⟨_, hd⟩
  have eres : Silmaril.Wasm.SingleThreaded.resume (Store.mapH gL s₁) tR' (.values []) =
      Silmaril.Wasm.SingleThreaded.resume s₁ t₁ (.values []) := by
    obtain ⟨x, hx⟩ := hdec
    rw [resume_congr hth' hx, resume_mapHG]
  obtain ⟨pos, tr₂, d₂, -⟩ := hostCall_lrunX (prof := prof) (g := HLinked2.logG unitG)
    (B := B) (th := th) (K := K) (segs := segs) (rest := rest) (y := (Store.mapH gL s₁, tR'))
    (p := fTy) (ws := [.u32 b]) (us := []) hB.lock hE hB.entry hi hleave hB.func rfl rfl
    (by decide) rfl rfl (by decide) rfl rfl (by decide) fWit_params fWit_result
  have eres' : (core3 neverFail).resume (Store.mapH gL s₁) tR' (.values (lowerArgs fTy.results [])) =
      Silmaril.Wasm.SingleThreaded.resume s₁ t₁ (.values []) := eres
  rw [eres'] at d₂
  have hrt := rt_resume hR' hsR
  rw [eres] at hrt
  exact ⟨b, rfl, _, _, d₁.trans d₂, ⟨hB.lock, hB.entry, ⟨st, hi, hleave⟩, hB.func⟩, rfl, hrt⟩

end Seg

/-! ## The start run -/

section Run

variable {prof : ProfileKind} {th : Option ThreadId}
  {K : List Flat → Canon.P (core3 neverFail) Σh (Ret (core3 neverFail))}
  {segs : List (Seg (core3 neverFail) Σh)} {rest : List (Activation (core3 neverFail) Σh)}

theorem internalP_eq : @Engine.CoreEngine.Internal (core3P (profile neverFail)) Nat =
    Internal neverFail := internalP_profileR

theorem resultOf_fFlat : Param.resultOf fFlat.results (some (.flat [])) = .values [] := rfl

/-- **The IR's start run with host calls, in the machine**: a start run of the IR whose import
calls are answered with no results, ending at a returned status (values or a trap), is matched
by a live run of the machine to the core activation at the same status, the host log extended by
one event per import call, the call of `f` on its `u32` argument (`coreLog`). -/
theorem startRun_ref {imps : CoreIface} (himps : imps.all (·.2 == fFlat) = true) :
    ∀ {c c' : (core3P (profile neverFail)).Config Nat}
      {ys : List (Σ _ : (sigN imps.length).Op, Option Payload)},
      Param.StartRunI (core3P (profile neverFail)) imps c ys c' →
      (∀ y ∈ ys, y.2 = some (.flat [])) →
      ∀ {r : Engine.CallResult}, (core3P (profile neverFail)).status c'.1 c'.2 = .returned r →
      ∀ {B : Machine.Config (core3 neverFail) Σh} {tR : STh}, CallInv B th →
      tR.config (Store.mapH gL c.1) = c.2.config (Store.mapH gL c.1) →
      RT (Store.mapH gL c.1) tR →
      ∃ (tr : List (Label (core3 neverFail) Σh)) (B' : Machine.Config (core3 neverFail) Σh)
        (tR' : STh),
        LRun prof (fun _ _ => false) (DG embL.host)
          (coreCfg B th K segs rest (Store.mapH gL c.1, tR)) tr
          (coreCfg B' th K segs rest (Store.mapH gL c'.1, tR')) ∧
        (core3 neverFail).status (Store.mapH gL c'.1) tR' = .returned r ∧ CallInv B' th ∧
        B'.host = (B.host.1, B.host.2 ++ coreLog ys) := by
  intro c c' ys hrun
  induction hrun with
  | @nil c c' run =>
    intro _ r hend B tR hB hth hR
    obtain ⟨s, t⟩ := c
    obtain ⟨s', t'⟩ := c'
    unfold Engine.CoreEngine.Steps at run
    rw [internalP_eq] at run
    obtain ⟨r', hr'⟩ := flatStatus_returned hend
    have hs' : status neverFail s' t' = .returned r' := (statusP_profile s' t').symm.trans hr'
    have hsm : status neverFail (Store.mapH gL s') t' = .returned r' := status_mapH_returned hs'
    obtain ⟨tR', tr, d, -, hth', hR', hC⟩ := run_ref (th := th) (K := K) (segs := segs)
      (rest := rest) (prof := prof) hB.lock run hth hR (by rw [hsm]; nofun)
    have e := statusE_flat neverFail (Store.mapH gL s') tR'
    rw [hC, hsm] at e
    have hend' : flatStatus (Silmaril.Wasm.Game.statusP (profile neverFail) s' t') =
        .returned r := hend
    rw [hr'] at hend'
    have e3 : flatStatus (Silmaril.Wasm.SingleThreaded.Status.returned
        (H := CanonHost (core3 neverFail)) r') = .returned r := by
      rcases r' with vs | _
      · simp only [flatStatus] at hend' ⊢
        cases hm : vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
        | none => rw [hm] at hend'; cases hend'
        | some fvs =>
          rw [hm] at hend'
          cases hend'
          rfl
      · simp only [flatStatus] at hend' ⊢
        cases hend'
        rfl
    exact ⟨tr, B, tR', d, e.trans e3, hB, by simp [coreLog]⟩
  | @call s s₁ t t₁ h args c'' cs run callout hh r rest' ih =>
    intro hans r₀ hend B tR hB hth hR
    unfold Engine.CoreEngine.Steps at run
    rw [internalP_eq] at run
    obtain ⟨b, rfl, tr₁, B₁, d₁, hB₁, hhost₁, hR₁⟩ := call_ref (th := th) (K := K) (segs := segs)
      (rest := rest) (prof := prof) hB run hth hR callout
    have hr : r = some (.flat []) := hans _ List.mem_cons_self
    subst hr
    have himp : imps[h].2 = fFlat := by
      have := List.all_eq_true.mp himps _ (List.getElem_mem hh)
      simpa using this
    have eres : (core3P (profile neverFail)).resume s₁ t₁
        (Param.resultOf imps[h].2.results (some (.flat []))) =
        Silmaril.Wasm.SingleThreaded.resume s₁ t₁ (.values []) := by
      rw [himp, resultOf_fFlat]
      rfl
    obtain ⟨tr₂, B₂, tR₂, d₂, hst₂, hB₂, hhost₂⟩ := ih (fun y hy => hans y (List.mem_cons_of_mem _ hy))
      hend (B := B₁) (tR := Silmaril.Wasm.SingleThreaded.resume s₁ t₁ (.values [])) hB₁
      (by rw [eres]) (by rw [eres]; exact hR₁)
    refine ⟨tr₁ ++ tr₂, B₂, tR₂, d₁.trans ?_, hst₂, hB₂, ?_⟩
    · rw [eres] at d₂
      exact d₂
    · rw [hhost₂, hhost₁]
      simp [coreLog, coreEvent]

end Run

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
