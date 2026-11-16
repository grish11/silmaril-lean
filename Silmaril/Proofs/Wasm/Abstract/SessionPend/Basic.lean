module

public import Silmaril.Wasm.Abstract.HostStrat.Thms
public import Silmaril.Wasm.Abstract.PubModule.Thms
public import Silmaril.Wasm.Abstract.LinkCore.Thms
public import Silmaril.Games.Abstract.ModuleInf.Thms

/-!
# The pending prefixes of the Core session (proofs)

* `satP_eraseTrap`: erasing trap stores keeps the call prefixes, so the call prefixes of the
  store-retaining Core triple are those of the Core triple (`satP_coreTripleS`), and each is a
  reached callout (`coreTripleS_satP_callout`, from `coreTriple_satP_callout`).
* `coreInf_prepend`: a finite labelled run in front of a productive run.
* `callout_satP` (deterministic profile, typed checked invocations): conversely, every reached
  callout is a call prefix. If the host leaves it pending, it is a pending call. Otherwise the
  host answers it, and the answered run continues: it ends at a stuck configuration, which is a
  value or trap end or a blocked callout (`hostSquare_stuck`), or it diverges, host-free after a
  log, at a host-divergent callout, or productively (`diverges_iff_obs`). Each of these is an
  observation whose log extends the callout's.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.SessionPend

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
  Silmaril.Wasm

universe u

/-- Erasing the stores of traps keeps the call prefixes. -/
theorem satP_eraseTrap {E : Sig.{u}} {S A B : Type u} (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) :
    StratObs.satP (StratSession.eraseTrap t) = StratObs.satP t := by
  funext s a
  ext x
  simp only [StratObs.satP, StratSession.eraseTrap, Set.mem_ofPred_eq, Set.mem_image,
    Prod.exists]
  constructor
  · rintro (h | h | ⟨d, e, ⟨d', e', h, hde⟩, hp⟩ | h)
    · exact .inl h
    · exact .inr (.inl h)
    · obtain ⟨rfl, -⟩ := Prod.mk.inj hde
      exact .inr (.inr (.inl ⟨d', e', h, hp⟩))
    · exact .inr (.inr (.inr h))
  · rintro (h | h | ⟨d, e, h, hp⟩ | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl ⟨d, _, ⟨d, e, h, rfl⟩, hp⟩))
    · exact .inr (.inr (.inr h))

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
  {Ok : Store H → Nat × List Val → Prop}

/-- The store-retaining Core triple has the call prefixes of the Core triple. -/
theorem satP_coreTripleS :
    StratObs.satP (coreTripleS P host Ok) = StratObs.satP (coreTriple P host Ok) := by
  rw [← satP_eraseTrap, eraseTrap_coreTripleS]

/-- **Every call prefix of the store-retaining Core triple is a reached callout.** -/
theorem coreTripleS_satP_callout {s : Store H} {q : Nat × List Val}
    {c : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op}
    (h : (c, m) ∈ StratObs.satP (coreTripleS P host Ok) s q) :
    Ok s q ∧ ∃ c', EvRun P host (invoke s q.1 q.2) c c' ∧ AtCallout c' m := by
  rw [satP_coreTripleS] at h
  exact coreTriple_satP_callout h

/-! ## Productive runs with a finite run in front -/

theorem coreInf_silent {x y : Config H} {ω : Nat → Call (wasmHostSig H)}
    (hs : HEvStep P host x none y) (h : CoreInf P host y ω) : CoreInf P host x ω := by
  obtain ⟨g, hg0, hg⟩ := h
  refine ⟨fun n => match n with | 0 => x | n + 1 => g (n + 1), rfl, fun n => ?_⟩
  rcases n with _ | n
  · obtain ⟨c₁, hr, he⟩ := hg 0
    rw [hg0] at hr
    exact ⟨c₁, .head hs hr, he⟩
  · exact hg (n + 1)

theorem coreInf_cons {x y : Config H} {e : Call (wasmHostSig H)} {ω : Nat → Call (wasmHostSig H)}
    (hs : HEvStep P host x (some e) y) (h : CoreInf P host y ω) :
    CoreInf P host x ([e] ++ω ω) := by
  obtain ⟨g, hg0, hg⟩ := h
  refine ⟨fun n => match n with | 0 => x | n + 1 => g n, rfl, fun n => ?_⟩
  rcases n with _ | n
  · refine ⟨x, .refl, ?_⟩
    have h0 : ([e] ++ω ω) 0 = e := Shape.streamAppend_lt (by simp)
    rw [h0]
    show HEvStep P host x (some e) (g 0)
    rw [hg0]; exact hs
  · have h1 : ([e] ++ω ω) (n + 1) = ω n := by
      rw [Shape.streamAppend_ge (by simp)]; simp
    rw [h1]
    exact hg n

/-- **A finite labelled run in front of a productive run.** -/
theorem coreInf_prepend {x y : Config H} {cs : List (Call (wasmHostSig H))}
    {ω : Nat → Call (wasmHostSig H)} (hr : EvRun P host x cs y) (h : CoreInf P host y ω) :
    CoreInf P host x (cs ++ω ω) := by
  induction hr with
  | refl => rwa [Shape.streamAppend_nil]
  | silent hs _ ih => exact coreInf_silent hs (ih h)
  | @event _ _ _ e cs hs _ ih =>
    have := coreInf_cons hs (ih h)
    rwa [← Shape.streamAppend_append] at this

theorem streamTake_streamAppend {α : Type} (c : List α) (e : α) (ω : Nat → α) :
    streamTake ((c ++ [e]) ++ω ω) c.length = c ∧ ((c ++ [e]) ++ω ω) c.length = e := by
  refine ⟨List.ext_getElem (by simp [streamTake]) fun i h₁ h₂ => ?_, ?_⟩
  · simp only [streamTake, List.getElem_ofFn]
    rw [Shape.streamAppend_lt (by simp; omega), List.getElem_append_left h₂]
  · rw [Shape.streamAppend_lt (by simp)]
    simp

/-! ## Reached callouts are call prefixes -/

section Det

variable {o : SingleThreaded.GrowOracle}

/-- **Every reached callout is a call prefix of the Core triple** (deterministic profile, typed
checked invocations, a host with typed answers in the native host slice). -/
theorem callout_satP (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    (hOk : ∀ s q, Ok s q → InvOk s q) {s : Store H} {q : Nat × List Val}
    {c : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op} (hq : Ok s q)
    {c' : Config H} (hr : EvRun (SingleThreaded.profile o) host (invoke s q.1 q.2) c c')
    (hat : AtCallout c' m) :
    (c, m) ∈ StratObs.satP (coreTriple (SingleThreaded.profile o) host Ok) s q := by
  obtain ⟨hs, hS, hok⟩ := hOk s q hq
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
  -- the host answers: the run goes on with the answer
  set e : Call (wasmHostSig H) := ⟨(hh, c'.store, us), (s'', r)⟩ with he
  have hstep : HEvStep (SingleThreaded.profile o) host c' (some e)
      ⟨s'', c'.frame, E.fill r.toAdmin⟩ := ⟨E, b, hd, rfl, hout, rfl⟩
  have hr₂ := evRun_trans hr (.event hstep (.refl _))
  -- every extension of the answered run has the prefix `c` then the call
  have hpre : ∀ cs₁, StratObs.CallPre c (hh, c'.store, us) ((c ++ [e]) ++ cs₁) :=
    fun cs₁ => ⟨(s'', r), cs₁, by simp [he]⟩
  rcases steps_stuck_or_diverges (P := SingleThreaded.profile o) (host := host)
      (c := ⟨s'', c'.frame, E.fill r.toAdmin⟩) with ⟨d, hsd, hend⟩ | hdv
  · obtain ⟨cs₁, hr₁⟩ := steps_iff_evRun.1 hsd
    have hr₃ := evRun_trans hr₂ hr₁
    obtain ⟨_, -, hcase⟩ := hostSquare_stuck (o := o) hT hH hs hS hok (evRun_steps hr₃) hend
    rcases hcase with ⟨e', -, hce⟩ | ⟨hh', us', hnat, E', a', hd'⟩
    · refine .inr (.inr (.inl ⟨_, e', ⟨hq, .inl ?_⟩, hpre cs₁⟩))
      rcases e' with ⟨ws | t, s₂⟩ | _ | _
      · obtain rfl : d = ⟨s₂, {}, vals ws⟩ := hce
        exact hr₃
      · exact hce.elim
      · obtain ⟨s₂, rfl⟩ := hce
        exact ⟨s₂, hr₃⟩
      · exact hce.elim
    · have hno' := coreHostRel_noAns_iff.1 hnat.2.2
      exact .inr (.inl ⟨_, _, ⟨hq, .inl ⟨d, E', a', hr₃, hd', rfl, hno'⟩⟩, hpre cs₁⟩)
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

/-- **The call prefixes of the store-retaining Core triple are the reached callouts**
(deterministic profile, typed checked invocations, a host with typed answers in the native host
slice). -/
theorem coreTripleS_satP_iff (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    (hOk : ∀ s q, Ok s q → InvOk s q) {s : Store H} {q : Nat × List Val}
    {c : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op} :
    (c, m) ∈ StratObs.satP (coreTripleS (SingleThreaded.profile o) host Ok) s q ↔
      Ok s q ∧ ∃ c', EvRun (SingleThreaded.profile o) host (invoke s q.1 q.2) c c' ∧
        AtCallout c' m := by
  refine ⟨coreTripleS_satP_callout, fun ⟨hq, c', hr, hat⟩ => ?_⟩
  rw [satP_coreTripleS]
  exact callout_satP hT hH hOk hq hr hat

end Det

end Silmaril.Proofs.Wasm.Abstract.SessionPend
