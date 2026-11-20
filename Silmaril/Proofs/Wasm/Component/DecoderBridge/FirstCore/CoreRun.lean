module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.Root
public import Silmaril.Wasm.SingleThreaded.Exec.StatusComplete
public import Silmaril.Wasm.SingleThreaded.Exec.InterpTyped

/-!
# A core activation of the concrete engine running to a trap in the machine

The reference machine of the decoded binaries runs core code with the concrete engine
`core3 o`, whose internal step is the interpreter step (`internalC (stepI o)`, a function) and
whose status is `statusE o`, the flat view of the interpreter status `statusC (stepI o)`.

* `runCI_complete`: completeness of the fuelled runner `runC (stepI o)` along any interpreter
  invariant (`InterpInv`, e.g. typing): a run of the single-threaded machine (`Internal o`) to a
  configuration that is not running is the runner's result for some fuel (the proof of
  `SingleThreaded.runC_complete`, whose hypotheses hold only under the invariant here);
* `uniqueStep_core`: a core activation whose status is `running` has exactly one step, the
  interpreter's;
* `lrun_runC`: a run of the fuelled runner is a live run of the core activation in the machine;
* `lrun_coreTrap`: when the runner's result is a trap, the machine reaches a configuration
  whose only step is the specification trap `coreTrap`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.SingleThreaded (GrowOracle Internal status statusC internalC runC
  NSteps tsize)
open Silmaril.Wasm.SingleThreaded.Exec (stepI InterpInv)
open Silmaril.Wasm.Execution.Core (Store Step Config)

/-! ## Completeness of the fuelled runner under an invariant -/

section Runner

variable {H : Type} {o : GrowOracle} {I : Config H → Prop}

/-- **Completeness of `runC (stepI o)` along an interpreter invariant.** -/
theorem runCI_complete (hI : InterpInv o I) {s s' : Store H}
    {t t' : Silmaril.Wasm.SingleThreaded.Thread} (hi : I (t.config s))
    (hr : Relation.ReflTransGen (Internal o) (s, t) (s', t'))
    (hst : status o s' t' ≠ .running) :
    ∃ n, runC (stepI o) n s t = (s', t', status o s' t') := by
  have hy : ∀ z, ¬ Internal o (s', t') z :=
    Silmaril.Wasm.SingleThreaded.status_ne_running_no_internal hst
  have hj : ∀ {x a b : Store H × Silmaril.Wasm.SingleThreaded.Thread}, Internal o x a →
      Internal o x b → Silmaril.Wasm.SingleThreaded.Det.Join (Internal o) a b :=
    fun ha hb => Silmaril.Wasm.SingleThreaded.Internal.deterministic ha hb
  have aux : ∀ (k m : Nat) (x : Store H × Silmaril.Wasm.SingleThreaded.Thread), tsize x = m →
      I (x.2.config x.1) → NSteps (Internal o) k x (s', t') →
      ∃ n, runC (stepI o) n x.1 x.2 = (s', t', status o s' t') := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
    rintro ⟨s₀, t₀⟩ hm hI₀ hk
    have hsound : ∀ c', stepI o (t₀.config s₀) = some c' →
        Step (Silmaril.Wasm.SingleThreaded.profile o) (fun _ _ _ _ => False) (t₀.config s₀) c' :=
      fun _ h => Silmaril.Wasm.SingleThreaded.Exec.stepI_sound (hI.storeOk _ hI₀)
        (hI.headInv _ hI₀) h
    have hcomplete : ∀ c', Step (Silmaril.Wasm.SingleThreaded.profile o) (fun _ _ _ _ => False)
        (t₀.config s₀) c' → (stepI o (t₀.config s₀)).isSome :=
      fun _ h => Silmaril.Wasm.SingleThreaded.Exec.stepI_complete (hI.storeOk _ hI₀)
        (hI.headInv _ hI₀) h
    have hsc : statusC (stepI o) s₀ t₀ = status o s₀ t₀ :=
      Silmaril.Wasm.SingleThreaded.Exec.statusI_eq_of hI hI₀
    by_cases hs0 : status o s₀ t₀ = .running
    · obtain ⟨⟨s₁', t₁'⟩, hx1'⟩ := Silmaril.Wasm.SingleThreaded.status_running_iff.mp hs0
      have hsome : (stepI o (t₀.config s₀)).isSome := by
        obtain ⟨f', code', -, hst'⟩ := hx1'
        exact hcomplete _ hst'
      obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hsome
      have hi' : internalC (stepI o) (s₀, t₀) = some (c'.store, .active c'.frame c'.code) := by
        simp [internalC, hc']
      have hx' := Silmaril.Wasm.SingleThreaded.internalC_sound o hsound hi'
      have hI₁ : I ((Silmaril.Wasm.SingleThreaded.Thread.active c'.frame c'.code).config
          c'.store) := hI.pres _ _ hI₀ (hsound c' hc')
      have hrun : ∀ n, runC (stepI o) (n + 1) s₀ t₀ =
          runC (stepI o) n c'.store (.active c'.frame c'.code) :=
        fun n => Silmaril.Wasm.SingleThreaded.runC_step (hsc.trans hs0) hi'
      cases hk with
      | refl => exact absurd hs0 hst
      | @head _ x1 _ j hx1 hrest =>
        rcases Silmaril.Wasm.SingleThreaded.Internal.shrink hx' hx1 with heq | hlt
        · subst heq
          obtain ⟨n, hn⟩ := ihk j (by omega) _ _ rfl hI₁ hrest
          exact ⟨n + 1, (hrun n).trans hn⟩
        · obtain ⟨m', hm', hpath⟩ :=
            Silmaril.Wasm.SingleThreaded.NSteps.of_step_join hj hy (.head hx1 hrest) hx'
          rcases Nat.lt_or_eq_of_le hm' with hlt' | rfl
          · obtain ⟨n, hn⟩ := ihk m' hlt' _ _ rfl hI₁ hpath
            exact ⟨n + 1, (hrun n).trans hn⟩
          · obtain ⟨n, hn⟩ := ihm _ (hm ▸ hlt) _ rfl hI₁ hpath
            exact ⟨n + 1, (hrun n).trans hn⟩
    · have hno := Silmaril.Wasm.SingleThreaded.status_ne_running_no_internal hs0
      cases hk with
      | refl =>
        refine ⟨1, ?_⟩
        rw [Silmaril.Wasm.SingleThreaded.runC_stop (by rw [hsc]; exact hs0), hsc]
      | head h _ => exact absurd h (hno _)
  obtain ⟨k, hk⟩ := Silmaril.Wasm.SingleThreaded.NSteps.of_rtg hr
  exact aux k _ (s, t) rfl hi hk

end Runner

/-! ## Core activations of the concrete engine in the machine -/

section Machine

variable {o : GrowOracle} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call (core3 o) → Canon.P (core3 o) σ (Ret (core3 o))}

/-- **A running core activation has exactly one step**, the interpreter's. -/
theorem uniqueStep_core {m : Machine.Config (core3 o) σ} {th : Option ThreadId}
    {ct : (core3 o).Thread (CanonHost (core3 o))}
    {k : List FlatValue → Canon.P (core3 o) σ (Ret (core3 o))} {segs : List (Seg (core3 o) σ)}
    {rest : List (Activation (core3 o) σ)}
    {y : Store (CanonHost (core3 o)) × Silmaril.Wasm.SingleThreaded.Thread}
    (hc : m.ctl = ⟨th, .core ct k, segs⟩ :: rest)
    (hs : (core3 o).status m.store.core ct = .running)
    (hi : internalC (stepI o) (m.store.core, ct) = some y) :
    UniqueStep prof hr dispatch m .core
      { m with store := { m.store with core := y.1 }, ctl := ⟨th, .core y.2 k, segs⟩ :: rest } := by
  refine ⟨.coreInternal hc (.inl hs) hi, fun l' m' h' => ?_⟩
  cases h' with
  | coreInternal hc' _ hi' =>
    rw [hc] at hc'
    obtain ⟨rfl, hf, rfl⟩ := Activation.mk.inj (List.cons.inj hc').1
    obtain ⟨rfl, rfl⟩ := Focus.core.inj hf
    obtain rfl := (List.cons.inj hc').2
    have := hi.symm.trans hi'
    cases this
    exact ⟨rfl, rfl⟩
  | coreReturned hc' hs' =>
    rw [hc] at hc'
    obtain ⟨rfl, hf, rfl⟩ := Activation.mk.inj (List.cons.inj hc').1
    obtain ⟨rfl, rfl⟩ := Focus.core.inj hf
    rw [hs] at hs'
    cases hs'
  | coreTrap hc' hs' =>
    rw [hc] at hc'
    obtain ⟨rfl, hf, rfl⟩ := Activation.mk.inj (List.cons.inj hc').1
    obtain ⟨rfl, rfl⟩ := Focus.core.inj hf
    rw [hs] at hs'
    cases hs'
  | coreCallout hc' hs' =>
    rw [hc] at hc'
    obtain ⟨rfl, hf, rfl⟩ := Activation.mk.inj (List.cons.inj hc').1
    obtain ⟨rfl, rfl⟩ := Focus.core.inj hf
    rw [hs] at hs'
    cases hs'
  | fault hf =>
    cases hf <;> simp_all
  | hostInvoke hrd => rw [hrd.1] at hc; cases hc
  | hostTick hrd => rw [hrd.1] at hc; cases hc
  | hostCancel hrd => rw [hrd.1] at hc; cases hc
  | hostRun hrd => rw [hrd.1] at hc; cases hc
  | _ => simp_all

theorem status_core3_running {H : Type} {s : Store H} {t : Silmaril.Wasm.SingleThreaded.Thread}
    (h : statusC (stepI o) s t = .running) : (core3 o).status s t = .running := by
  show Core3.statusE o s t = _
  unfold Core3.statusE
  rw [h]

theorem status_core3_trap {H : Type} {s : Store H} {t : Silmaril.Wasm.SingleThreaded.Thread}
    (h : statusC (stepI o) s t = .returned .trap) : (core3 o).status s t = .returned .trap := by
  show Core3.statusE o s t = _
  unfold Core3.statusE
  rw [h]

/-- **A run of the fuelled runner is a live run of the core activation.** -/
theorem lrun_runC {th : Option ThreadId}
    {k : List FlatValue → Canon.P (core3 o) σ (Ret (core3 o))} {segs : List (Seg (core3 o) σ)}
    {rest : List (Activation (core3 o) σ)} :
    ∀ (n : Nat) {s s' : Store (CanonHost (core3 o))} {t t' : Silmaril.Wasm.SingleThreaded.Thread}
      {st : Silmaril.Wasm.SingleThreaded.Status (CanonHost (core3 o))},
      runC (stepI o) n s t = (s', t', st) → ∀ (M : Machine.Config (core3 o) σ),
      M.ctl = ⟨th, .core t k, segs⟩ :: rest → M.store.core = s → M.store.lockdown = false →
      ∃ tr, LRun prof hr dispatch M tr
        { M with store := { M.store with core := s' }, ctl := ⟨th, .core t' k, segs⟩ :: rest } ∧
        traceObs tr = []
  | 0, s, s', t, t', st, h, M, hc, hcore, _ => by
    simp only [runC, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    refine ⟨[], ?_, rfl⟩
    obtain ⟨S, h₀, conts, ctl, pending, results, cancels⟩ := M
    dsimp only at hc hcore ⊢
    subst hc hcore
    exact .refl _
  | n + 1, s, s', t, t', st, h, M, hc, hcore, hl => by
    have stop : (s, t) = (s', t') → ∃ tr, LRun prof hr dispatch M tr
        { M with store := { M.store with core := s' }, ctl := ⟨th, .core t' k, segs⟩ :: rest } ∧
        traceObs tr = [] := by
      intro e
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      refine ⟨[], ?_, rfl⟩
      obtain ⟨S, h₀, conts, ctl, pending, results, cancels⟩ := M
      dsimp only at hc hcore ⊢
      subst hc hcore
      exact .refl _
    unfold runC at h
    cases hs : statusC (stepI o) s t with
    | running =>
      rw [hs] at h
      dsimp only at h
      cases hin : internalC (stepI o) (s, t) with
      | none =>
        rw [hin] at h
        simp only [Prod.mk.injEq] at h
        exact stop (by rw [h.1, h.2.1])
      | some p =>
        obtain ⟨s₁, t₁⟩ := p
        rw [hin] at h
        have hst : (core3 o).status M.store.core t = .running := by
          rw [hcore]; exact status_core3_running hs
        have hi' : internalC (stepI o) (M.store.core, t) = some (s₁, t₁) := by rw [hcore]; exact hin
        have u := uniqueStep_core (prof := prof) (hr := hr) (dispatch := dispatch) hc hst hi'
        obtain ⟨tr, r, hob⟩ := lrun_runC n h
          { M with store := { M.store with core := s₁ }, ctl := ⟨th, .core t₁ k, segs⟩ :: rest }
          rfl rfl hl
        exact ⟨_, .cons ⟨by rw [hc]; exact List.cons_ne_nil _ _, hl⟩ u r, by
          simpa [traceObs, Label.obs?] using hob⟩
    | returned r =>
      rw [hs] at h
      simp only [Prod.mk.injEq] at h
      exact stop (by rw [h.1, h.2.1])
    | callout hh args =>
      rw [hs] at h
      simp only [Prod.mk.injEq] at h
      exact stop (by rw [h.1, h.2.1])
    | stuck =>
      rw [hs] at h
      simp only [Prod.mk.injEq] at h
      exact stop (by rw [h.1, h.2.1])

/-- **A runner result that traps**: the machine reaches a live configuration whose only step is
the specification trap `coreTrap`. -/
theorem lrun_coreTrap {th : Option ThreadId}
    {k : List FlatValue → Canon.P (core3 o) σ (Ret (core3 o))} {segs : List (Seg (core3 o) σ)}
    {rest : List (Activation (core3 o) σ)} {n : Nat} {s s' : Store (CanonHost (core3 o))}
    {t t' : Silmaril.Wasm.SingleThreaded.Thread}
    (h : runC (stepI o) n s t = (s', t', .returned .trap))
    (hs' : statusC (stepI o) s' t' = .returned .trap) (M : Machine.Config (core3 o) σ)
    (hc : M.ctl = ⟨th, .core t k, segs⟩ :: rest) (hcore : M.store.core = s)
    (hl : M.store.lockdown = false) :
    ∃ tr mT, LRun prof hr dispatch M tr mT ∧ Live mT ∧
      UniqueStep prof hr dispatch mT (.trap .coreTrap) (trapCfg mT) := by
  obtain ⟨tr, r, -⟩ := lrun_runC n h M hc hcore hl
  have hst : (core3 o).status s' t' = .returned .trap := status_core3_trap hs'
  refine ⟨tr, _, r, ⟨List.cons_ne_nil _ _, hl⟩, UniqueStep.of_core rfl ?_ (.coreTrap rfl hst)⟩
  show (core3 o).status s' t' ≠ _ ∧ (core3 o).status s' t' ≠ _
  rw [hst]
  exact ⟨nofun, nofun⟩

end Machine

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
