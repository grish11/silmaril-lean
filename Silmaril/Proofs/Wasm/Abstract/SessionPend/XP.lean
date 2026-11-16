module

public import Silmaril.Proofs.Wasm.Abstract.SessionPend.Basic
public import Silmaril.Wasm.Abstract.HostSessionXP.Thms
public import Silmaril.Wasm.Abstract.PubModuleXP.Thms
public import Silmaril.Wasm.Abstract.HostClosingXP.Thms
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Execution.Core.Soundness

/-!
# The pending prefixes of the Core session with exceptions (proofs)

* `stuck_cases` (every profile, a host with typed answers, a typed invocation): a stuck
  configuration reached from the invocation is terminal (values, an uncaught exception or a
  trap, in some frame) or at a host call the host has no outcome for. By type safety
  (`Steps.safe`) for the totalized host (`hostOk_totalize`): a step of the totalized host that
  the host does not make is a host call without outcome.
* `callout_satPXP` (deterministic profile, `Ok → InvOkXP tags`, a host with typed answers in the
  host slices): every reached callout is a call prefix of the Core triple with exceptions, as
  `callout_satP`. Terminal ends move to the empty frame through the canonical closure
  (`evRun_wasmEvFunXP_vals` and `wasmEvFunXP_vals_iff`, and their exception and trap forms).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.SessionPend

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
  Silmaril.Wasm

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
  {Ok : Store H → Nat × List Val → Prop}

/-- **The stuck ends of a typed invocation**: terminal, or a host call without host outcome. -/
theorem stuck_cases (hT : HostTyped host) {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hok : InvokeOk s a vs) {d : Config H}
    (hrun : Steps P host (invoke s a vs) d) (hend : ∀ d', ¬ Step P host d d') :
    (∃ r : Result, d.code = r.toAdmin) ∨
      ∃ (E : SingleThreaded.Ctx) (a' : Nat) (hh : H) (us : List Val),
        SingleThreaded.decompose? d.store d.code = some (E, a', hh, us) ∧
        ∀ o, ¬ host hh d.store us o := by
  obtain ⟨_, _, _, -, -, hc⟩ := invoke_ok hs hok
  have hrun' : Steps P (totalize host) (invoke s a vs) d := by
    clear hend
    induction hrun with
    | refl => exact .refl
    | tail _ h ih => exact .tail ih (Step.host_mono (fun _ _ _ _ h => Or.inl h) h)
  rcases (Steps.safe (hostOk_totalize hT) hc hrun').2 with hterm | ⟨d', hst⟩
  · exact .inl hterm
  obtain ⟨e, he⟩ := step_hEvStep hst
  cases e with
  | none =>
    rcases he with he | ⟨rfl, E, a', hh, us, hd, hdiv⟩
    · exact absurd (Step.host_mono (fun _ _ _ _ h => h.elim) he) (hend _)
    · rcases hdiv with hdiv | ⟨-, hno⟩
      · exact absurd (hEvStep_step (P := P) (host := host) (e := none)
          (Or.inr ⟨rfl, E, a', hh, us, hd, hdiv⟩)) (hend _)
      · exact .inr ⟨E, a', hh, us, hd, hno⟩
  | some e =>
    obtain ⟨E, a', hd, hst', hans, hc'⟩ := he
    rcases hans with hans | ⟨he', -⟩
    · exact absurd (hEvStep_step (P := P) (host := host) (e := some e)
        ⟨E, a', hd, hst', hans, hc'⟩) (hend _)
    · cases he'

/-- The store-retaining Core triple with exceptions has the call prefixes of the Core triple
with exceptions. -/
theorem satP_coreTripleSXP :
    StratObs.satP (coreTripleSXP P host Ok) = StratObs.satP (coreTripleXP P host Ok) := by
  rw [← satP_eraseTrap, eraseTrap_coreTripleSXP]

/-- **Every call prefix of the store-retaining Core triple with exceptions is a reached
callout.** -/
theorem coreTripleSXP_satP_callout {s : Store H} {q : Nat × List Val}
    {c : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op}
    (h : (c, m) ∈ StratObs.satP (coreTripleSXP P host Ok) s q) :
    Ok s q ∧ ∃ c', EvRun P host (invoke s q.1 q.2) c c' ∧ AtCallout c' m := by
  rw [satP_coreTripleSXP] at h
  exact coreTripleXP_satP_callout h

section Det

variable {o : SingleThreaded.GrowOracle} {tags : List TagInst}

/-- **Every reached callout is a call prefix of the Core triple with exceptions**
(deterministic profile, `InvOkXP tags`, a host with typed answers in the host slices). -/
theorem callout_satPXP (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    (hE : Interp.HostSliceE tags host) (hOk : ∀ s q, Ok s q → InvOkXP tags s q)
    {s : Store H} {q : Nat × List Val}
    {c : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op} (hq : Ok s q)
    {c' : Config H} (hr : EvRun (SingleThreaded.profile o) host (invoke s q.1 q.2) c c')
    (hat : AtCallout c' m) :
    (c, m) ∈ StratObs.satP (coreTripleXP (SingleThreaded.profile o) host Ok) s q := by
  obtain ⟨hs, hS, hts, hok⟩ := hOk s q hq
  obtain ⟨hh, s', us⟩ := m
  obtain ⟨E, b, hd, hst⟩ := hat
  simp only at hd hst
  subst hst
  by_cases hdiv : host hh c'.store us .diverged
  · exact .inl ⟨hq, .inr ⟨c', E, b, hr, hd, rfl, hdiv⟩⟩
  by_cases hno : ∀ o, ¬ host hh c'.store us o
  · exact .inl ⟨hq, .inl ⟨c', E, b, hr, hd, rfl, hno⟩⟩
  push Not at hno
  obtain ⟨out, hout⟩ := hno
  rcases out with ⟨s'', r⟩ | _
  swap
  · exact (hdiv hout).elim
  set e : Call (wasmHostSig H) := ⟨(hh, c'.store, us), (s'', r)⟩ with he
  have hstep : HEvStep (SingleThreaded.profile o) host c' (some e)
      ⟨s'', c'.frame, E.fill r.toAdmin⟩ := ⟨E, b, hd, rfl, hout, rfl⟩
  have hr₂ := evRun_trans hr (.event hstep (.refl _))
  have hpre : ∀ cs₁, StratObs.CallPre c (hh, c'.store, us) ((c ++ [e]) ++ cs₁) :=
    fun cs₁ => ⟨(s'', r), cs₁, by simp [he]⟩
  rcases steps_stuck_or_diverges (P := SingleThreaded.profile o) (host := host)
      (c := ⟨s'', c'.frame, E.fill r.toAdmin⟩) with ⟨d, hsd, hend⟩ | hdv
  · obtain ⟨cs₁, hr₁⟩ := steps_iff_evRun.1 hsd
    have hr₃ := evRun_trans hr₂ hr₁
    have hcons := evRun_consistent hr₃
    rcases stuck_cases hT hs hok (evRun_steps hr₃) hend with ⟨r', hcode⟩ | ⟨E', a', hh', us', hd', hno'⟩
    · obtain ⟨ds, df, dc⟩ := d
      simp only at hcode
      subst hcode
      rcases r' with ws | t | _
      · have h₁ := evRun_wasmEvFunXP_vals hT hH hE hs hS hts hok hr₃
        have h₂ := (wasmEvFunXP_vals_iff (o := o) hT hH hE hs hS hts hok).1 ⟨h₁, hcons⟩
        exact .inr (.inr (.inl ⟨_, .ret (.inl ws) ds, ⟨hq, .inl h₂⟩, hpre cs₁⟩))
      · have h₁ := evRun_wasmEvFunXP_throw hT hH hE hs hS hts hok hr₃
        have h₂ := (wasmEvFunXP_throw_iff (o := o) hT hH hE hs hS hts hok).1 ⟨h₁, hcons⟩
        exact .inr (.inr (.inl ⟨_, .ret (.inr t) ds, ⟨hq, .inl h₂⟩, hpre cs₁⟩))
      · have h₁ := evRun_wasmEvFunXP_trap hT hH hE hs hS hts hok hr₃
        have h₂ := (wasmEvFunXP_trap_iff (o := o) hT hH hE hs hS hts hok).1 ⟨h₁, hcons⟩
        exact .inr (.inr (.inl ⟨_, .trap, ⟨hq, .inl h₂⟩, hpre cs₁⟩))
    · exact .inr (.inl ⟨_, (hh', d.store, us'), ⟨hq, .inl ⟨d, E', a', hr₃, hd', rfl, hno'⟩⟩,
        hpre cs₁⟩)
  · rcases diverges_iff_obs.1 hdv with ⟨cs₁, c₁, hr₁, hfree⟩ | ⟨cs₁, c₁, hr₁, m', hat', hdm⟩ |
        ⟨ω, hω⟩
    · exact .inr (.inr (.inl ⟨_, .div, ⟨hq, .inr ⟨rfl, c₁, evRun_trans hr₂ hr₁, hfree⟩⟩,
        hpre cs₁⟩))
    · obtain ⟨hh', s₁, us'⟩ := m'
      obtain ⟨E', a', hd', hs₁⟩ := hat'
      exact .inr (.inl ⟨_, _, ⟨hq, .inr ⟨c₁, E', a', evRun_trans hr₂ hr₁, hd', hs₁,
        hs₁ ▸ hdm⟩⟩, hpre cs₁⟩)
    · obtain ⟨htake, hat⟩ := streamTake_streamAppend c e ω
      refine .inr (.inr (.inr ⟨_, ⟨hq, coreInf_prepend hr₂ hω⟩, c.length, htake, ?_⟩))
      rw [hat]

/-- **The call prefixes of the store-retaining Core triple with exceptions are the reached
callouts** (deterministic profile, `InvOkXP tags`, a host with typed answers in the host
slices). -/
theorem coreTripleSXP_satP_iff (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    (hE : Interp.HostSliceE tags host) (hOk : ∀ s q, Ok s q → InvOkXP tags s q)
    {s : Store H} {q : Nat × List Val} {c : List (Call (wasmHostSig H))}
    {m : (wasmHostSig H).Op} :
    (c, m) ∈ StratObs.satP (coreTripleSXP (SingleThreaded.profile o) host Ok) s q ↔
      Ok s q ∧ ∃ c', EvRun (SingleThreaded.profile o) host (invoke s q.1 q.2) c c' ∧
        AtCallout c' m := by
  refine ⟨coreTripleSXP_satP_callout, fun ⟨hq, c', hr, hat⟩ => ?_⟩
  rw [satP_coreTripleSXP]
  exact callout_satPXP hT hH hE hOk hq hr hat

end Det

end Silmaril.Proofs.Wasm.Abstract.SessionPend
