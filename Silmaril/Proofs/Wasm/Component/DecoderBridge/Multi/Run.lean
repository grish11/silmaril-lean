module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Start

/-!
# The IR's start run in the machine, with the store it leaves

`FirstImp.Start.startRun_ref` runs a start run of the IR with host calls in the reference machine
but forgets the store around the core activation except `CallInv`. The epilogue of the start call
(`Multi.Start.start_atG`) needs it: each host call only replaces the host state and appends one
subtask and one caller record (`Callout.hostCall_lrunX`). Here:

* `Ext B B'`: `B'` is `B` with the host state replaced and subtasks and caller records appended;
* `call_refX`, `startRun_refX`: `call_ref`, `startRun_ref` with `Ext B B'`, and the typing of the
  final thread (`RT`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
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

/-! ## Store extensions -/

section Ext

variable {E : CoreEngine} {σ : Type}

/-- `B'` is `B` with the host state replaced and subtasks and caller records appended. -/
def Ext (B B' : Machine.Config E σ) : Prop :=
  ∃ (h : σ) (xs : List Subtask) (cs : List (Caller E)),
    B' = { B with host := h, store := { B.store with
      subtasks := B.store.subtasks ++ xs, callers := B.store.callers ++ cs } }

theorem Ext.refl (B : Machine.Config E σ) : Ext B B := by
  refine ⟨B.host, [], [], ?_⟩
  obtain ⟨S, h, conts, ctl, pending, results, cancels⟩ := B
  simp

theorem Ext.trans {B₁ B₂ B₃ : Machine.Config E σ} (h₁ : Ext B₁ B₂) (h₂ : Ext B₂ B₃) :
    Ext B₁ B₃ := by
  obtain ⟨h, xs, cs, rfl⟩ := h₁
  obtain ⟨h', xs', cs', rfl⟩ := h₂
  exact ⟨h', xs ++ xs', cs ++ cs', by simp⟩

end Ext

/-! ## The IR's start run, with the store -/

section Run

variable {prof : ProfileKind} {th : Option ThreadId}
  {K : List Flat → Canon.P (core3 neverFail) Σh (Ret (core3 neverFail))}
  {segs : List (Seg (core3 neverFail) Σh)} {rest : List (Activation (core3 neverFail) Σh)}

/-- `call_ref`, with the store it leaves. -/
theorem call_refX {B : Machine.Config (core3 neverFail) Σh} (hB : CallInv B th)
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
        traceObs tr = [] ∧ CallInv B' th ∧ B'.host = (B.host.1, B.host.2 ++ [(⟨0⟩, [toRefVal (.u32 b)], [])]) ∧
        Ext B B' ∧
        RT (Store.mapH gL s₁) (Silmaril.Wasm.SingleThreaded.resume s₁ t₁ (.values [])) := by
  obtain ⟨args', hst', hfl⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.flatStatus_eq_callout' hco
  have hs₁ : status neverFail s₁ t₁ = .callout h args' := (statusP_profile s₁ t₁).symm.trans hst'
  have hsm : status neverFail (Store.mapH gL s₁) t₁ = .callout lowH args' :=
    status_mapH_callout hs₁
  obtain ⟨tR', tr₁, d₁, hob₁, hth', hR', hC⟩ := run_ref (th := th) (K := K) (segs := segs)
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
  obtain ⟨pos, tr₂, d₂, hob₂⟩ := hostCall_lrunX (prof := prof) (g := HLinked2.logG unitG)
    (B := B) (th := th) (K := K) (segs := segs) (rest := rest) (y := (Store.mapH gL s₁, tR'))
    (p := fTy) (ws := [.u32 b]) (us := []) hB.lock hE hB.entry hi hleave hB.func rfl rfl
    (by decide) rfl rfl (by decide) rfl rfl (by decide) fWit_params fWit_result
  have eres' : (core3 neverFail).resume (Store.mapH gL s₁) tR' (.values (lowerArgs fTy.results [])) =
      Silmaril.Wasm.SingleThreaded.resume s₁ t₁ (.values []) := eres
  rw [eres'] at d₂
  have hrt := rt_resume hR' hsR
  rw [eres] at hrt
  refine ⟨b, rfl, _, _, d₁.trans d₂, ?_, ⟨hB.lock, hB.entry, ⟨st, hi, hleave⟩, hB.func⟩, rfl,
    ⟨_, _, _, rfl⟩, hrt⟩
  simp only [traceObs] at hob₁ hob₂ ⊢
  simp only [List.filterMap_append, List.filterMap_cons, Label.obs?, hob₁, hob₂, List.nil_append]

/-- **`startRun_ref`, with the store it leaves and the typing of the final thread.** -/
theorem startRun_refX {imps : CoreIface} (himps : imps.all (·.2 == fFlat) = true) :
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
          (coreCfg B' th K segs rest (Store.mapH gL c'.1, tR')) ∧ traceObs tr = [] ∧
        (core3 neverFail).status (Store.mapH gL c'.1) tR' = .returned r ∧ CallInv B' th ∧
        B'.host = (B.host.1, B.host.2 ++ coreLog ys) ∧ Ext B B' ∧
        RT (Store.mapH gL c'.1) tR' := by
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
    obtain ⟨tR', tr, d, hob, hth', hR', hC⟩ := run_ref (th := th) (K := K) (segs := segs)
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
    exact ⟨tr, B, tR', d, hob, e.trans e3, hB, by simp [coreLog], Ext.refl B, hR'⟩
  | @call s s₁ t t₁ h args c'' cs run callout hh r rest' ih =>
    intro hans r₀ hend B tR hB hth hR
    unfold Engine.CoreEngine.Steps at run
    rw [internalP_eq] at run
    obtain ⟨b, rfl, tr₁, B₁, d₁, hob₁, hB₁, hhost₁, hX₁, hR₁⟩ := call_refX (th := th) (K := K)
      (segs := segs) (rest := rest) (prof := prof) hB run hth hR callout
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
    obtain ⟨tr₂, B₂, tR₂, d₂, hob₂, hst₂, hB₂, hhost₂, hX₂, hR₂⟩ :=
      ih (fun y hy => hans y (List.mem_cons_of_mem _ hy))
      hend (B := B₁) (tR := Silmaril.Wasm.SingleThreaded.resume s₁ t₁ (.values [])) hB₁
      (by rw [eres]) (by rw [eres]; exact hR₁)
    refine ⟨tr₁ ++ tr₂, B₂, tR₂, d₁.trans ?_, ?_, hst₂, hB₂, ?_, hX₁.trans hX₂, hR₂⟩
    · rw [eres] at d₂
      exact d₂
    · simp only [traceObs] at hob₁ hob₂ ⊢
      simp only [List.filterMap_append, hob₁, hob₂, List.nil_append]
    · rw [hhost₂, hhost₁]
      simp [coreLog, coreEvent]

end Run

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
