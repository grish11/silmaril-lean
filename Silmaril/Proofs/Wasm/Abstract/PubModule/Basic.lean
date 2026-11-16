module

public import Silmaril.Wasm.Abstract.PubModule.Defs
public import Silmaril.Games.Abstract.StratObs.Thms
public import Silmaril.Wasm.Abstract.HostCall.Thms

/-!
# The public interaction equivalence of an export (proofs)

* Splitting a labelled run at an event (`evRun_split`): every call of a run, of a pending call,
  or of a productive stream is made at a reached callout (`satP_callout`).
* The Core triple is recovered from its call prefixes: its pending calls are the call prefixes
  the host leaves pending (`core_pending_eq`). A triple with this property is determined by its
  saturation (`eq_of_sat_eq`).
* The public triple has the call prefixes of the underlying triple (`satP_pubTriple`), and two
  public triples are equal iff the underlying triples agree at the two exports
  (`pubTriple_eq_iff`); for the Core triple this is the agreement of the Core observations
  (`coreTriple_at_eq_iff`), which is `PubEquiv` (`pubEquiv_iff`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.PubModule

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

universe u

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
  {Ok : Store H → Nat × List Val → Prop}

/-! ## Runs split at an event -/

theorem evRun_split {c c' : Config H} {l : List (Call (wasmHostSig H))}
    (h : EvRun P host c l c') :
    ∀ {cs cs' : List (Call (wasmHostSig H))} {e : Call (wasmHostSig H)}, l = cs ++ e :: cs' →
      ∃ c₁ c₂, EvRun P host c cs c₁ ∧ HEvStep P host c₁ (some e) c₂ ∧
        EvRun P host c₂ cs' c' := by
  induction h with
  | refl => intro cs cs' e hl; simp at hl
  | silent h₁ _ ih =>
    intro cs cs' e hl
    obtain ⟨c₁, c₂, h₁', h₂, h₃⟩ := ih hl
    exact ⟨c₁, c₂, .silent h₁ h₁', h₂, h₃⟩
  | event h₁ hr ih =>
    intro cs cs' e hl
    cases cs with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      exact ⟨_, _, .refl _, h₁, hr⟩
    | cons x cs =>
      simp only [List.cons_append, List.cons.injEq] at hl
      obtain ⟨rfl, hl⟩ := hl
      obtain ⟨c₁, c₂, h₁', h₂, h₃⟩ := ih hl
      exact ⟨c₁, c₂, .event h₁ h₁', h₂, h₃⟩

theorem atCallout_of_hEvStep {c c' : Config H} {e : Call (wasmHostSig H)}
    (h : HEvStep P host c (some e) c') :
    AtCallout c e.1 ∧ host e.1.1 e.1.2.1 e.1.2.2 (.returned e.2.1 e.2.2) := by
  obtain ⟨E, b, hd, hs, hh, -⟩ := h
  exact ⟨⟨E, b, hd, hs.symm⟩, by rw [hs]; exact hh⟩

theorem evRun_of_silent {c c' : Config H}
    (h : Relation.ReflTransGen (fun a b => HEvStep P host a none b) c c') :
    EvRun P host c [] c' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl _
  | head h _ ih => exact .silent h ih

/-- A call made in a run is made at a reached callout, and answered by the host. -/
theorem callout_of_callPre {c c' : Config H} {d cs : List (Call (wasmHostSig H))}
    {m : (wasmHostSig H).Op} (h : EvRun P host c d c') (hp : StratObs.CallPre cs m d) :
    ∃ c₁, EvRun P host c cs c₁ ∧ AtCallout c₁ m ∧ ∃ n : (wasmHostSig H).Ar m,
      host m.1 m.2.1 m.2.2 (.returned n.1 n.2) := by
  obtain ⟨n, cs', rfl⟩ := hp
  obtain ⟨c₁, _, h₁, h₂, -⟩ := evRun_split h rfl
  exact ⟨c₁, h₁, (atCallout_of_hEvStep h₂).1, n, (atCallout_of_hEvStep h₂).2⟩

/-! ## Membership in the Core triple -/

theorem mem_core1 {s : Store H} {q : Nat × List Val}
    {x : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)} :
    x ∈ (coreTriple P host Ok).1 s q ↔ Ok s q ∧ (CoreObsL P host s q.1 q.2 (.done x.1 x.2) ∨
      (x.2 = .div ∧ CoreObsL P host s q.1 q.2 (.div x.1))) := Iff.rfl

theorem mem_core2 {s : Store H} {q : Nat × List Val}
    {x : List (Call (wasmHostSig H)) × (wasmHostSig H).Op} :
    x ∈ (coreTriple P host Ok).2.1 s q ↔ Ok s q ∧ (CoreObsL P host s q.1 q.2 (.blocked x.1 x.2) ∨
      CoreObsL P host s q.1 q.2 (.hostDiv x.1 x.2)) := Iff.rfl

theorem mem_core3 {s : Store H} {q : Nat × List Val} {ω : Nat → Call (wasmHostSig H)} :
    ω ∈ (coreTriple P host Ok).2.2 s q ↔ Ok s q ∧ CoreObsL P host s q.1 q.2 (.prod ω) := Iff.rfl

theorem run_of_done {s : Store H} {a : Nat} {vs : List Val} {d : List (Call (wasmHostSig H))}
    {e : End (Store H) (List Val ⊕ Nat)} (h : CoreObsL P host s a vs (.done d e)) :
    ∃ c, EvRun P host (invoke s a vs) d c :=
  match e, h with
  | .ret (.inl _) _, h => ⟨_, h⟩
  | .ret (.inr _) _, h => (h : False).elim
  | .trap, ⟨_, h⟩ => ⟨_, h⟩
  | .div, h => (h : False).elim

/-- A pending Core call is a reached callout the host leaves pending. -/
theorem pend_callout {s : Store H} {q : Nat × List Val}
    {x : List (Call (wasmHostSig H)) × (wasmHostSig H).Op}
    (h : x ∈ (coreTriple P host Ok).2.1 s q) :
    Ok s q ∧ (∃ c, EvRun P host (invoke s q.1 q.2) x.1 c ∧ AtCallout c x.2) ∧
      HostPends host x.2 := by
  obtain ⟨cs, hh, s₁, us⟩ := x
  obtain ⟨hq, ⟨c, E, b, hr, hd, hs, hn⟩ | ⟨c, E, b, hr, hd, hs, hn⟩⟩ := mem_core2.1 h
  · exact ⟨hq, ⟨c, hr, E, b, hd, hs⟩, .inl hn⟩
  · exact ⟨hq, ⟨c, hr, E, b, hd, hs⟩, .inr hn⟩

/-- **Every call prefix of the Core triple is a reached callout.** -/
theorem satP_callout {s : Store H} {q : Nat × List Val}
    {x : List (Call (wasmHostSig H)) × (wasmHostSig H).Op}
    (h : x ∈ StratObs.satP (coreTriple P host Ok) s q) :
    Ok s q ∧ ∃ c, EvRun P host (invoke s q.1 q.2) x.1 c ∧ AtCallout c x.2 := by
  rcases h with h | ⟨d, m', h, hp⟩ | ⟨d, e, h, hp⟩ | ⟨ω, h, k, hk, hm⟩
  · exact ⟨(pend_callout h).1, (pend_callout h).2.1⟩
  · obtain ⟨hq, ⟨c, hr, -⟩, -⟩ := pend_callout h
    obtain ⟨c₁, h₁, h₂, -⟩ := callout_of_callPre hr hp
    exact ⟨hq, c₁, h₁, h₂⟩
  · obtain ⟨hq, h | ⟨-, h⟩⟩ := mem_core1.1 h
    · obtain ⟨c, hr⟩ := run_of_done h
      obtain ⟨c₁, h₁, h₂, -⟩ := callout_of_callPre hr hp
      exact ⟨hq, c₁, h₁, h₂⟩
    · obtain ⟨c, hr, -⟩ := h
      obtain ⟨c₁, h₁, h₂, -⟩ := callout_of_callPre hr hp
      exact ⟨hq, c₁, h₁, h₂⟩
  · obtain ⟨hq, hω⟩ := mem_core3.1 h
    obtain ⟨c', hr, g, hg0, hg⟩ := coreInf_prefix hω k
    obtain ⟨c₁, hrt, hev⟩ := hg 0
    have hr' := evRun_trans hr (evRun_of_silent (hg0 ▸ hrt))
    rw [List.append_nil] at hr'
    refine ⟨hq, c₁, ?_, ?_⟩
    · rw [← hk]; exact hr'
    · rw [← hm]; exact (atCallout_of_hEvStep hev).1

/-- **The pending Core calls are the call prefixes the host leaves pending.** -/
theorem core_pending_eq (s : Store H) (q : Nat × List Val) :
    (coreTriple P host Ok).2.1 s q =
      {x | x ∈ StratObs.satP (coreTriple P host Ok) s q ∧ HostPends host x.2} := by
  ext ⟨cs, hh, s₁, us⟩
  constructor
  · intro h; exact ⟨.inl h, (pend_callout h).2.2⟩
  · rintro ⟨h, hp⟩
    obtain ⟨hq, c, hr, E, b, hd, hs⟩ := satP_callout h
    rcases hp with hp | hp
    · exact mem_core2.2 ⟨hq, .inl ⟨c, E, b, hr, hd, hs, hp⟩⟩
    · exact mem_core2.2 ⟨hq, .inr ⟨c, E, b, hr, hd, hs, hp⟩⟩

/-- The Core triple is saturated exactly when the host leaves every call prefix pending. -/
theorem core_saturated_iff :
    StratObs.Saturated (coreTriple P host Ok) ↔
      ∀ s q x, x ∈ StratObs.satP (coreTriple P host Ok) s q → HostPends host x.2 := by
  rw [StratObs.saturated_iff]
  constructor
  · intro h s q x hx
    rw [h] at hx
    exact (pend_callout hx).2.2
  · intro h
    funext s q
    rw [core_pending_eq s q]
    ext x
    exact ⟨fun hx => ⟨hx, h s q x hx⟩, fun hx => hx.1⟩

/-- **The obstruction to saturation**: a returning run that makes a host call the host answers
and does not diverge on. -/
theorem core_not_saturated {s : Store H} {q : Nat × List Val}
    {cs cs' : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op}
    {n : (wasmHostSig H).Ar m} {ws : List Val} {s₂ : Store H} (hq : Ok s q)
    (h : EvRun P host (invoke s q.1 q.2) (cs ++ ⟨m, n⟩ :: cs') ⟨s₂, {}, vals ws⟩)
    (hd : ¬ host m.1 m.2.1 m.2.2 .diverged) :
    ¬ StratObs.Saturated (coreTriple P host Ok) := by
  intro hs
  have hp := core_saturated_iff.1 hs s q (cs, m)
    (.inr (.inr (.inl ⟨_, .ret (.inl ws) s₂, mem_core1.2 ⟨hq, .inl h⟩, n, cs', rfl⟩)))
  obtain ⟨-, -, -, n', hn⟩ := callout_of_callPre h ⟨n, cs', rfl⟩
  rcases hp with hp | hp
  · exact hp _ hn
  · exact hd hp

/-! ## Triples determined by their saturation -/

theorem eq_of_sat_eq {E : Sig.{u}} {S A B : Type u} {t t' : ObsTriple E S A B}
    {R : E.Op → Prop}
    (ht : ∀ s a, t.2.1 s a = {x | x ∈ StratObs.satP t s a ∧ R x.2})
    (ht' : ∀ s a, t'.2.1 s a = {x | x ∈ StratObs.satP t' s a ∧ R x.2})
    (h : StratObs.sat t = StratObs.sat t') : t = t' := by
  have h2 : StratObs.satP t = StratObs.satP t' := congrArg (fun t => t.2.1) h
  refine Prod.ext (congrArg (fun t => t.1) h)
    (Prod.ext (funext fun s => funext fun a => ?_) (congrArg (fun t => t.2.2) h))
  rw [ht, ht', h2]

theorem coreStrat_eq_iff {P' : Silmaril.Wasm.Numerics.Profile}
    {Ok' : Store H → Nat × List Val → Prop} :
    coreStrat P host Ok = coreStrat P' host Ok' ↔ coreTriple P host Ok = coreTriple P' host Ok' :=
  ⟨fun h => eq_of_sat_eq (fun s q => core_pending_eq s q) (fun s q => core_pending_eq s q)
    (StratObs.toDStrat_eq_iff.1 h), fun h => congrArg StratObs.toDStrat h⟩

/-! ## The public triple -/

theorem pubEnd_injective {S B : Type} :
    Function.Injective (pubEnd : End S B → End PUnit (B × S)) := by
  intro e e' h
  cases e <;> cases e' <;> simp_all [pubEnd]

theorem pubEnd_surj {S B : Type} (e : End PUnit (B × S)) : ∃ e', pubEnd e' = e := by
  rcases e with ⟨⟨b, s⟩, ⟨⟩⟩ | _ | _
  exacts [⟨.ret b s, rfl⟩, ⟨.trap, rfl⟩, ⟨.div, rfl⟩]

variable {T : ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat)}

theorem mem_pubTriple_fst {s : Store H} {a : Nat} {u : PUnit} {vs : List Val}
    {d : List (Call (wasmHostSig H))} {e : End (Store H) (List Val ⊕ Nat)} :
    (d, pubEnd e) ∈ (pubTriple T s a).1 u vs ↔ (d, e) ∈ T.1 s (a, vs) :=
  ⟨fun ⟨_, h, he⟩ => pubEnd_injective he ▸ h, fun h => ⟨e, h, rfl⟩⟩

theorem satP_pubTriple (s : Store H) (a : Nat) (u : PUnit) (vs : List Val) :
    StratObs.satP (pubTriple T s a) u vs = StratObs.satP T s (a, vs) := by
  ext x
  constructor
  · rintro (h | h | ⟨d, e, ⟨e', h, -⟩, hp⟩ | h)
    exacts [.inl h, .inr (.inl h), .inr (.inr (.inl ⟨d, e', h, hp⟩)), .inr (.inr (.inr h))]
  · rintro (h | h | ⟨d, e, h, hp⟩ | h)
    exacts [.inl h, .inr (.inl h), .inr (.inr (.inl ⟨d, pubEnd e, ⟨e, h, rfl⟩, hp⟩)),
      .inr (.inr (.inr h))]

theorem pubTriple_eq_iff {s s' : Store H} {a a' : Nat} :
    pubTriple T s a = pubTriple T s' a' ↔ ∀ vs,
      T.1 s (a, vs) = T.1 s' (a', vs) ∧ T.2.1 s (a, vs) = T.2.1 s' (a', vs) ∧
        T.2.2 s (a, vs) = T.2.2 s' (a', vs) := by
  constructor
  · intro h vs
    refine ⟨Set.ext fun ⟨d, e⟩ => ?_,
      congrFun (congrFun (congrArg (fun t => t.2.1) h) PUnit.unit) vs,
      congrFun (congrFun (congrArg (fun t => t.2.2) h) PUnit.unit) vs⟩
    rw [← mem_pubTriple_fst (u := PUnit.unit), h, mem_pubTriple_fst]
  · intro h
    refine Prod.ext (funext fun u => funext fun vs => Set.ext fun ⟨d, e⟩ => ?_)
      (Prod.ext (funext fun _ => funext fun vs => (h vs).2.1)
        (funext fun _ => funext fun vs => (h vs).2.2))
    obtain ⟨e, rfl⟩ := pubEnd_surj e
    rw [mem_pubTriple_fst, mem_pubTriple_fst, (h vs).1]

theorem corePub_pending_eq (s : Store H) (a : Nat) (u : PUnit) (vs : List Val) :
    (pubTriple (coreTriple P host Ok) s a).2.1 u vs =
      {x | x ∈ StratObs.satP (pubTriple (coreTriple P host Ok) s a) u vs ∧ HostPends host x.2} := by
  rw [satP_pubTriple]; exact core_pending_eq s (a, vs)

/-! ## Agreement of the Core observations -/

/-- One direction of `coreTriple_at_eq_iff`: inclusions of the components give inclusions of
the observations. -/
theorem obs_of_sub {s s' : Store H} {q q' : Nat × List Val}
    (h1 : (coreTriple P host Ok).1 s q ⊆ (coreTriple P host Ok).1 s' q')
    (h2 : (coreTriple P host Ok).2.1 s q ⊆ (coreTriple P host Ok).2.1 s' q')
    (h3 : (coreTriple P host Ok).2.2 s q ⊆ (coreTriple P host Ok).2.2 s' q') (o : FullObs H) :
    Ok s q ∧ CoreObsL P host s q.1 q.2 o → Ok s' q' ∧ CoreObsL P host s' q'.1 q'.2 o := by
  rintro ⟨hq, ho⟩
  match o, ho with
  | .done d e, ho =>
    obtain ⟨hq', ho' | ⟨rfl, -⟩⟩ := mem_core1.1 (@h1 (d, e) (mem_core1.2 ⟨hq, .inl ho⟩))
    · exact ⟨hq', ho'⟩
    · exact (ho : False).elim
  | .blocked d (hh, s₁, us), ho =>
    obtain ⟨hq', ho' | ho'⟩ := mem_core2.1 (@h2 (d, hh, s₁, us) (mem_core2.2 ⟨hq, .inl ho⟩))
    · exact ⟨hq', ho'⟩
    · obtain ⟨-, -, -, -, -, -, hn⟩ := ho
      obtain ⟨-, -, -, -, -, -, hn'⟩ := ho'
      exact (hn _ hn').elim
  | .hostDiv d (hh, s₁, us), ho =>
    obtain ⟨hq', ho' | ho'⟩ := mem_core2.1 (@h2 (d, hh, s₁, us) (mem_core2.2 ⟨hq, .inr ho⟩))
    · obtain ⟨-, -, -, -, -, -, hn⟩ := ho
      obtain ⟨-, -, -, -, -, -, hn'⟩ := ho'
      exact (hn' _ hn).elim
    · exact ⟨hq', ho'⟩
  | .div d, ho =>
    obtain ⟨hq', ho' | ⟨-, ho'⟩⟩ :=
      mem_core1.1 (@h1 (d, .div) (mem_core1.2 ⟨hq, .inr ⟨rfl, ho⟩⟩))
    · exact (ho' : False).elim
    · exact ⟨hq', ho'⟩
  | .prod ω, ho => exact mem_core3.1 (h3 (mem_core3.2 ⟨hq, ho⟩))

/-- The other direction: inclusions of the observations give inclusions of the components. -/
theorem sub_of_obs {s s' : Store H} {q q' : Nat × List Val}
    (h : ∀ o, Ok s q ∧ CoreObsL P host s q.1 q.2 o → Ok s' q' ∧ CoreObsL P host s' q'.1 q'.2 o) :
    (coreTriple P host Ok).1 s q ⊆ (coreTriple P host Ok).1 s' q' ∧
      (coreTriple P host Ok).2.1 s q ⊆ (coreTriple P host Ok).2.1 s' q' ∧
      (coreTriple P host Ok).2.2 s q ⊆ (coreTriple P host Ok).2.2 s' q' := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun ω hω => mem_core3.2 (h _ (mem_core3.1 hω))⟩
  · obtain ⟨hq, ho | ⟨he, ho⟩⟩ := mem_core1.1 hx
    · obtain ⟨hq', ho'⟩ := h _ ⟨hq, ho⟩
      exact mem_core1.2 ⟨hq', .inl ho'⟩
    · obtain ⟨hq', ho'⟩ := h _ ⟨hq, ho⟩
      exact mem_core1.2 ⟨hq', .inr ⟨he, ho'⟩⟩
  · obtain ⟨hq, ho | ho⟩ := mem_core2.1 hx
    · obtain ⟨hq', ho'⟩ := h _ ⟨hq, ho⟩
      exact mem_core2.2 ⟨hq', .inl ho'⟩
    · obtain ⟨hq', ho'⟩ := h _ ⟨hq, ho⟩
      exact mem_core2.2 ⟨hq', .inr ho'⟩

theorem coreTriple_at_eq_iff {s s' : Store H} {q q' : Nat × List Val} :
    ((coreTriple P host Ok).1 s q = (coreTriple P host Ok).1 s' q' ∧
      (coreTriple P host Ok).2.1 s q = (coreTriple P host Ok).2.1 s' q' ∧
      (coreTriple P host Ok).2.2 s q = (coreTriple P host Ok).2.2 s' q') ↔
      ∀ o, (Ok s q ∧ CoreObsL P host s q.1 q.2 o) ↔
        (Ok s' q' ∧ CoreObsL P host s' q'.1 q'.2 o) := by
  constructor
  · rintro ⟨h1, h2, h3⟩ o
    exact ⟨obs_of_sub h1.subset h2.subset h3.subset o,
      obs_of_sub h1.symm.subset h2.symm.subset h3.symm.subset o⟩
  · intro h
    obtain ⟨a1, a2, a3⟩ := sub_of_obs fun o => (h o).1
    obtain ⟨b1, b2, b3⟩ := sub_of_obs fun o => (h o).2
    exact ⟨a1.antisymm b1, a2.antisymm b2, a3.antisymm b3⟩

theorem pubEquiv_iff {s s' : Store H} {a a' : Nat} :
    PubEquiv P host Ok s a s' a' ↔ ∀ vs o,
      (Ok s (a, vs) ∧ CoreObsL P host s a vs o) ↔
        (Ok s' (a', vs) ∧ CoreObsL P host s' a' vs o) := by
  constructor
  · intro h vs o
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h vs
    match o with
    | .done cs (.ret (.inl ws) s₂) => exact h1 cs ws s₂
    | .done _ (.ret (.inr _) _) =>
      exact ⟨fun ⟨_, h⟩ => (h : False).elim, fun ⟨_, h⟩ => (h : False).elim⟩
    | .done cs .trap => exact h2 cs
    | .done _ .div => exact ⟨fun ⟨_, h⟩ => (h : False).elim, fun ⟨_, h⟩ => (h : False).elim⟩
    | .blocked cs (hh, s₁, us) => exact h3 cs hh s₁ us
    | .hostDiv cs (hh, s₁, us) => exact h4 cs hh s₁ us
    | .div cs => exact h5 cs
    | .prod ω => exact h6 ω
  · intro h vs
    exact ⟨fun cs ws s₂ => h vs (.done cs (.ret (.inl ws) s₂)), fun cs => h vs (.done cs .trap),
      fun cs hh s₁ us => h vs (.blocked cs (hh, s₁, us)),
      fun cs hh s₁ us => h vs (.hostDiv cs (hh, s₁, us)), fun cs => h vs (.div cs),
      fun ω => h vs (.prod ω)⟩

/-- **The public injection.** -/
theorem pubStrat_eq_iff {s s' : Store H} {a a' : Nat} :
    pubStrat P host Ok s a = pubStrat P host Ok s' a' ↔ PubEquiv P host Ok s a s' a' := by
  unfold pubStrat
  rw [StratObs.toDStrat_eq_iff, pubEquiv_iff]
  constructor
  · intro h vs
    exact coreTriple_at_eq_iff.1 (pubTriple_eq_iff.1
      (eq_of_sat_eq (corePub_pending_eq s a) (corePub_pending_eq s' a') h) vs)
  · intro h
    exact congrArg StratObs.sat (pubTriple_eq_iff.2 fun vs => coreTriple_at_eq_iff.2 (h vs))

/-! ## Reading back the public strategy -/

theorem pubStrat_mem_ret {s : Store H} {a : Nat} (vs : List Val)
    (cs : List (Call (wasmHostSig H))) (ws : List Val) (s₂ : Store H) :
    (.inr (.ask (PUnit.unit, vs)) :: (StratObs.callMoves cs ++
        [.inr (.ans (PUnit.unit, vs) (.inl (((.inl ws : List Val ⊕ Nat), s₂), PUnit.unit)))]) :
        List (Move (wasmHostSig H) (pubSig H))) ∈ (pubStrat P host Ok s a).toStrategy ↔
      Ok s (a, vs) ∧ EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ :=
  (StratObs.mem_ret _ vs cs _ _).trans <|
    (mem_pubTriple_fst (e := .ret (.inl ws) s₂)).trans <| mem_core1.trans <| by
      simp [CoreObsL]

theorem pubStrat_mem_inf {s : Store H} {a : Nat} (vs : List Val)
    (ω : Nat → Call (wasmHostSig H)) :
    StratObs.streamPlay [] (PUnit.unit, vs) ω ∈ (pubStrat P host Ok s a).inf ↔
      Ok s (a, vs) ∧ CoreInf P host (invoke s a vs) ω :=
  StratObs.mem_inf (PUnit.unit, vs) ω

end Silmaril.Proofs.Wasm.Abstract.PubModule
