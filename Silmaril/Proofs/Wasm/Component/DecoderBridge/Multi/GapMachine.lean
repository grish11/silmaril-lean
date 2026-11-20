module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.GapCore
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Run

/-!
# The IR's start run in the shared core store, in the machine

`Multi.Run.startRun_refX` runs the IR's start run of the **first** node in the machine, whose core
store is the IR's store with renamed host code (`Store.mapH gL`). For a later node the machine's
core store is the IR's store mapped into the shared store (`Gap.rel`, `Multi.GapShift`), and its
threads are the mapped threads (`gC`). Here:

* `GapThr g s t tR`: the machine's thread `tR` in `g.rel (mapH gL s)` is the map of the IR's thread
  `t` in `s`, which is good (`Reference.SplitGood`, at the machine's host type);
* `run_gap`: an internal run of the IR is a live run of the core activation to the mapped end;
* `call_gapX`: an import call of the IR is the callout of the mapped thread to the trampoline,
  answered `()` by the logging host, and the activation resumes with the mapped resumed thread;
* **`startRun_gapX`**: the IR's start run with its import calls, as `Run.startRun_refX`.
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
open Silmaril.Wasm.Execution.Core (Store FuncInst StoreOk ConfigOk Config)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "Σh" => Unit × List HLinked2.HostEvent
local notation "CH" => CanonHost (core3 neverFail)

/-! ## Related threads -/

/-- **The machine's thread is the map of the IR's**: in the shared store `g.rel (mapH gL s)`, the
configuration of `tR` is the map of `t`'s in `s` (host code renamed); `t` is good, the first `b`
functions of the shared store are the IR's imports (`Gap.PreOk`). -/
structure GapThr (g : Gap CH) (s : Store Nat) (t tR : STh) : Prop where
  cfg : tR.config (g.rel (Store.mapH FirstImp.gL s)) =
    gC g (t.config (Store.mapH FirstImp.gL s))
  good : SplitGood (t.config (Store.mapH FirstImp.gL s))
  pre : g.PreOk (Store.mapH FirstImp.gL s).funcs

/-- Internal runs of the IR are internal runs of its store with renamed host code. -/
theorem internal_mapH :
    ∀ {x y : Store Nat × STh}, Relation.ReflTransGen (Internal neverFail) x y →
      Relation.ReflTransGen (Internal neverFail) (Store.mapH FirstImp.gL x.1, x.2)
        (Store.mapH FirstImp.gL y.1, y.2) := by
  intro x y h
  induction h with
  | refl => exact .refl
  | @tail b c _ hst ih =>
    obtain ⟨s, t⟩ := b
    obtain ⟨s', t'⟩ := c
    obtain ⟨f', code', rfl, hs⟩ := hst
    refine ih.tail ⟨f', code', rfl, ?_⟩
    rw [config_mapHG]
    exact Step.mapH (P := profile neverFail) FirstImp.gL hs

theorem val_eq_num {δ : GShift} {v : Silmaril.Wasm.Execution.Core.Val}
    {n : Silmaril.Wasm.Execution.Core.NumVal} (h : δ.val v = .num n) : v = .num n := by
  cases v <;> simp_all [GShift.val]

section Run

variable {prof : ProfileKind} {th : Option ThreadId}
  {K : List Flat → Canon.P (core3 neverFail) Σh (Ret (core3 neverFail))}
  {segs : List (Seg (core3 neverFail) Σh)} {rest : List (Activation (core3 neverFail) Σh)}

/-- **An internal run of the IR, in the shared store**: the core activation runs to the mapped
end of the run, typed. -/
theorem run_gap {B : Machine.Config (core3 neverFail) Σh} (hl : B.store.lockdown = false)
    (g : Gap CH) (hinj : Function.Injective g.sh.fn) {s s₁ : Store Nat} {t t₁ tR : STh}
    (hrun : Relation.ReflTransGen (Internal neverFail) (s, t) (s₁, t₁))
    (hG : GapThr g s t tR) (hR : RT (g.rel (Store.mapH FirstImp.gL s)) tR)
    (hend : ∀ tR' : STh, tR'.config (g.rel (Store.mapH FirstImp.gL s₁)) =
      gC g (t₁.config (Store.mapH FirstImp.gL s₁)) →
      status neverFail (g.rel (Store.mapH FirstImp.gL s₁)) tR' ≠ .running) :
    ∃ tR' tr, LRun prof (fun _ _ => false) (DG embL.host)
        (coreCfg B th K segs rest (g.rel (Store.mapH FirstImp.gL s), tR)) tr
        (coreCfg B th K segs rest (g.rel (Store.mapH FirstImp.gL s₁), tR')) ∧ traceObs tr = [] ∧
      GapThr g s₁ t₁ tR' ∧ RT (g.rel (Store.mapH FirstImp.gL s₁)) tR' ∧
      statusC (stepI neverFail) (g.rel (Store.mapH FirstImp.gL s₁)) tR' =
        status neverFail (g.rel (Store.mapH FirstImp.gL s₁)) tR' := by
  have h₀ := internal_mapH hrun
  obtain ⟨tR', hr, hcfg, hgood, hfs⟩ := internal_gap g h₀ hG.good hG.pre hinj hG.cfg
  obtain ⟨hs₁, ht₁⟩ := Silmaril.Wasm.SingleThreaded.reachable_typed hr hR.store hR.thread
  have hfun := funcs_stepsG hr
  have hR' : RT (g.rel (Store.mapH FirstImp.gL s₁)) tR' := ⟨hs₁, ht₁, fun fi hfi => hR.hosts fi (by
    simp only at hfun; rw [← hfun]; exact hfi)⟩
  have hG' : GapThr g s₁ t₁ tR' := ⟨hcfg, hgood, by rw [hfs]; exact hG.pre⟩
  obtain ⟨n, hn⟩ := runCI_complete (I := fun c => ConfigOk c [])
    Silmaril.Wasm.SingleThreaded.Exec.typedInv' hR.thread hr (hend tR' hcfg)
  obtain ⟨tr, d, hob⟩ := lrun_runC (prof := prof) (hr := fun _ _ => false) (dispatch := DG embL.host)
    (k := K) (segs := segs) (rest := rest) (th := th) n hn
    (coreCfg B th K segs rest (g.rel (Store.mapH FirstImp.gL s), tR)) rfl rfl hl
  refine ⟨tR', tr, d, hob, hG', hR', ?_⟩
  rw [Silmaril.Wasm.SingleThreaded.Exec.statusI_eq_typed hR'.thread]

/-- **An import call of the IR's start run, in the shared store**: the core activation runs to the
callout of the mapped thread to the trampoline, the logging host answers `()` to the call of `f`
and logs it, and the activation resumes with the mapped resumed thread. -/
theorem call_gapX {B : Machine.Config (core3 neverFail) Σh} (hB : CallInv B th)
    (g : Gap CH) (hinj : Function.Injective g.sh.fn) {s s₁ : Store Nat} {t t₁ tR : STh}
    (hrun : Relation.ReflTransGen (Internal neverFail) (s, t) (s₁, t₁))
    (hG : GapThr g s t tR) (hR : RT (g.rel (Store.mapH FirstImp.gL s)) tR) {h : Nat}
    {args : List Flat}
    (hco : (core3P (profile neverFail)).status s₁ t₁ = .callout h args) :
    ∃ b : BitVec 32, args = [⟨.int .i32, b⟩] ∧
      ∃ (tr : List (Label (core3 neverFail) Σh)) (B' : Machine.Config (core3 neverFail) Σh)
        (tR' : STh),
        LRun prof (fun _ _ => false) (DG embL.host)
          (coreCfg B th K segs rest (g.rel (Store.mapH FirstImp.gL s), tR)) tr
          (coreCfg B' th K segs rest (g.rel (Store.mapH FirstImp.gL s₁), tR')) ∧ traceObs tr = [] ∧
        GapThr g s₁ (Silmaril.Wasm.SingleThreaded.resume s₁ t₁ (.values [])) tR' ∧
        CallInv B' th ∧ B'.host = (B.host.1, B.host.2 ++ [(⟨0⟩, [toRefVal (.u32 b)], [])]) ∧
        Ext B B' ∧ RT (g.rel (Store.mapH FirstImp.gL s₁)) tR' := by
  obtain ⟨args', hst', hfl⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.flatStatus_eq_callout' hco
  have hs₁ : status neverFail s₁ t₁ = .callout h args' := (statusP_profile s₁ t₁).symm.trans hst'
  have hsm : status neverFail (Store.mapH FirstImp.gL s₁) t₁ = .callout lowH args' :=
    status_mapH_callout hs₁
  have hfs : (Store.mapH FirstImp.gL s₁).funcs = (Store.mapH FirstImp.gL s).funcs :=
    funcs_stepsG (internal_mapH hrun)
  have hP₁ : g.PreOk (Store.mapH FirstImp.gL s₁).funcs := by rw [hfs]; exact hG.pre
  obtain ⟨tR', tr₁, d₁, hob₁, hG', hR', hC⟩ := run_gap (th := th) (K := K) (segs := segs)
    (rest := rest) (prof := prof) hB.lock g hinj hrun hG hR (fun tR' hc => by
      rw [(status_gap_callout g hP₁ hc hsm).1]; nofun)
  obtain ⟨hsR, E, a, hd, hd'⟩ := status_gap_callout g hG'.pre hG'.cfg hsm
  obtain ⟨b, hb⟩ := args_of_callout hR' hsR
  have ha' : args' = [.num ⟨.int .i32, b⟩] := by
    rcases args' with _ | ⟨v, _ | ⟨w, ws⟩⟩
    · cases hb
    · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hb
      rw [val_eq_num hb]
    · simp at hb
  subst ha'
  simp only [List.mapM_cons, List.mapM_nil, Silmaril.Wasm.SingleThreaded.toFlat?] at hfl
  cases hfl
  have hsR' : status neverFail (g.rel (Store.mapH FirstImp.gL s₁)) tR' =
      .callout lowH [.num ⟨.int .i32, b⟩] := by
    rw [hsR]; rfl
  have hE : (core3 neverFail).status (g.rel (Store.mapH FirstImp.gL s₁)) tR' =
      .callout lowH [⟨.int .i32, b⟩] := by
    have e := statusE_flat neverFail (g.rel (Store.mapH FirstImp.gL s₁)) tR'
    rw [hC, hsR'] at e
    exact e
  obtain ⟨st, hi, hleave⟩ := hB.inst
  obtain ⟨pos, tr₂, d₂, hob₂⟩ := hostCall_lrunX (prof := prof) (g := HLinked2.logG unitG)
    (B := B) (th := th) (K := K) (segs := segs) (rest := rest)
    (y := (g.rel (Store.mapH FirstImp.gL s₁), tR'))
    (p := fTy) (ws := [.u32 b]) (us := []) hB.lock hE hB.entry hi hleave hB.func rfl rfl
    (by decide) rfl rfl (by decide) rfl rfl (by decide) fWit_params fWit_result
  have eres : (core3 neverFail).resume (g.rel (Store.mapH FirstImp.gL s₁)) tR'
      (.values (lowerArgs fTy.results [])) =
      Silmaril.Wasm.SingleThreaded.resume (g.rel (Store.mapH FirstImp.gL s₁)) tR' (.values []) :=
    rfl
  rw [eres] at d₂
  have hrt := rt_resume hR' hsR
  have hcfg := resume_gap g hG'.cfg hd hd'
  rw [resume_mapHG] at hcfg
  have hgood := splitGood_resume hG'.good hd
  rw [resume_mapHG] at hgood
  refine ⟨b, rfl, _, _, _, d₁.trans d₂, ?_, ⟨hcfg, hgood, hG'.pre⟩,
    ⟨hB.lock, hB.entry, ⟨st, hi, hleave⟩, hB.func⟩, rfl, ⟨_, _, _, rfl⟩, hrt⟩
  simp only [traceObs] at hob₁ hob₂ ⊢
  simp only [List.filterMap_append, List.filterMap_cons, Label.obs?, hob₁, hob₂, List.nil_append]

/-- **The IR's start run in the shared store**, with the store it leaves and the typing of the
final thread (`Run.startRun_refX` for a later node). -/
theorem startRun_gapX {imps : CoreIface} (himps : imps.all (·.2 == fFlat) = true)
    (g : Gap CH) (hinj : Function.Injective g.sh.fn) :
    ∀ {c c' : (core3P (profile neverFail)).Config Nat}
      {ys : List (Σ _ : (sigN imps.length).Op, Option Payload)},
      Param.StartRunI (core3P (profile neverFail)) imps c ys c' →
      (∀ y ∈ ys, y.2 = some (.flat [])) →
      ∀ {fvs : List Flat},
        (core3P (profile neverFail)).status c'.1 c'.2 = .returned (.values fvs) →
      ∀ {B : Machine.Config (core3 neverFail) Σh} {tR : STh}, CallInv B th →
      GapThr g c.1 c.2 tR → RT (g.rel (Store.mapH FirstImp.gL c.1)) tR →
      ∃ (tr : List (Label (core3 neverFail) Σh)) (B' : Machine.Config (core3 neverFail) Σh)
        (tR' : STh),
        LRun prof (fun _ _ => false) (DG embL.host)
          (coreCfg B th K segs rest (g.rel (Store.mapH FirstImp.gL c.1), tR)) tr
          (coreCfg B' th K segs rest (g.rel (Store.mapH FirstImp.gL c'.1), tR')) ∧ traceObs tr = [] ∧
        (core3 neverFail).status (g.rel (Store.mapH FirstImp.gL c'.1)) tR' =
          .returned (.values fvs) ∧
        GapThr g c'.1 c'.2 tR' ∧ CallInv B' th ∧
        B'.host = (B.host.1, B.host.2 ++ coreLog ys) ∧ Ext B B' ∧
        RT (g.rel (Store.mapH FirstImp.gL c'.1)) tR' := by
  intro c c' ys hrun
  induction hrun with
  | @nil c c' run =>
    intro _ fvs hend B tR hB hG hR
    obtain ⟨s, t⟩ := c
    obtain ⟨s', t'⟩ := c'
    unfold Engine.CoreEngine.Steps at run
    rw [internalP_eq] at run
    obtain ⟨r', hr'⟩ := flatStatus_returned hend
    have hend' : flatStatus (Silmaril.Wasm.Game.statusP (profile neverFail) s' t') =
        .returned (.values fvs) := hend
    rw [hr'] at hend'
    obtain ⟨vs, rfl, hvs⟩ : ∃ vs, r' = .values vs ∧
        vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some fvs := by
      rcases r' with vs | _
      · simp only [flatStatus] at hend'
        cases hm : vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
        | none => rw [hm] at hend'; cases hend'
        | some fvs' =>
          rw [hm] at hend'
          cases hend'
          exact ⟨vs, rfl, hm⟩
      · simp only [flatStatus] at hend'
        cases hend'
    have hs' : status neverFail s' t' = .returned (.values vs) :=
      (statusP_profile s' t').symm.trans hr'
    have hsm : status neverFail (Store.mapH FirstImp.gL s') t' = .returned (.values vs) :=
      status_mapH_returned hs'
    obtain ⟨tR', tr, d, hob, hG', hR', hC⟩ := run_gap (th := th) (K := K) (segs := segs)
      (rest := rest) (prof := prof) hB.lock g hinj run hG hR (fun tR' hc => by
        rw [status_gap_values g hc hsm]; nofun)
    have hsR := status_gap_values g hG'.cfg hsm
    have hmap : (vs.map g.sh.val).mapM Silmaril.Wasm.SingleThreaded.toFlat? = some fvs := by
      rw [← hvs]
      clear hvs hs' hsm hsR hend' hr'
      induction vs with
      | nil => rfl
      | cons v vs ih =>
        simp only [List.map_cons, List.mapM_cons, ih]
        cases v <;> rfl
    have e := statusE_flat neverFail (g.rel (Store.mapH FirstImp.gL s')) tR'
    rw [hC, hsR] at e
    refine ⟨tr, B, tR', d, hob, ?_, hG', hB, by simp [coreLog], Ext.refl B, hR'⟩
    show Silmaril.Wasm.Component.Engine.Core3.statusE neverFail _ tR' = _
    rw [e]
    simp only [flatStatus, hmap]
  | @call s s₁ t t₁ h args c'' cs run callout hh r rest' ih =>
    intro hans fvs hend B tR hB hG hR
    unfold Engine.CoreEngine.Steps at run
    rw [internalP_eq] at run
    obtain ⟨b, rfl, tr₁, B₁, tR₁, d₁, hob₁, hG₁, hB₁, hhost₁, hX₁, hR₁⟩ := call_gapX (th := th) (K := K)
      (segs := segs) (rest := rest) (prof := prof) hB g hinj run hG hR callout
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
    obtain ⟨tr₂, B₂, tR₂, d₂, hob₂, hst₂, hG₂, hB₂, hhost₂, hX₂, hR₂⟩ :=
      ih (fun y hy => hans y (List.mem_cons_of_mem _ hy))
      hend (B := B₁) (tR := tR₁) hB₁ (by rw [eres]; exact hG₁) hR₁
    refine ⟨tr₁ ++ tr₂, B₂, tR₂, d₁.trans d₂, ?_, hst₂, hG₂, hB₂, ?_, hX₁.trans hX₂, hR₂⟩
    · simp only [traceObs] at hob₁ hob₂ ⊢
      simp only [List.filterMap_append, hob₁, hob₂, List.nil_append]
    rw [hhost₂, hhost₁]
    simp [coreLog, coreEvent]

end Run

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
