module

public import Silmaril.Wasm.Abstract.NodeLegal.Defs
public import Silmaril.Wasm.Abstract.NodeBridge.Thms
public import Silmaril.Wasm.Abstract.InstSession.Thms
public import Silmaril.Wasm.Game.Determinism.Thms
public import Silmaril.Games.Abstract.SessionLegal.Thms
public import Silmaril.Proofs.Wasm.Abstract.NodeBridge.Basic
public import Silmaril.Proofs.Wasm.Abstract.InstStrat.Basic

/-!
# Host-answer domains of an instance session (proofs)

See `Silmaril.Wasm.Abstract.NodeLegal.Thms`.

**Call stores.** A Core run viewing an import log passes, for each import call, through the
hidden state `.waiting a s t e` of the instance whose store `s` is the store recorded in the Core
event (`seg_bwd_waiting`, `waiting_of_split`, `waiting_of_mem`). With `Path.functional` (the
hidden state after a play is unique at `profile o`) this makes the Core-event legality of a
witness the same as `RoundLegal` of the log it views (`coreLegal_iff`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.NodeLegal

open Silmaril Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract Silmaril.Wasm.Abstract.NodeBridge Silmaril.Wasm.Abstract.NodeLegal
open Silmaril.Wasm.Abstract.InstSession (Res instTripleS)
open Silmaril.Proofs.Wasm.Abstract.NodeBridge (EvRunE evRun_iff silent_reach)
open Silmaril.Wasm.Numerics (Profile)

variable {I : ScalarInstance} {P : Profile} {Q : Store Nat → Result → Prop}

/-! ## Call stores along a Core run -/

section Waiting

/-- `NodeBridge.seg_bwd` with the waiting state: its store is the store of the Core event. -/
theorem seg_bwd_waiting {a : I.F.Op} {s : Store Nat} {t : Thread} {x : Call I.E}
    {ev : Call (wasmHostSig Nat)} {c₁ c₂ : Config Nat} (hv : CallView I x ev)
    (h₁ : Relation.ReflTransGen (fun a b => HEvStep P (instHost I) a none b) (t.config s) c₁)
    (h₂ : HEvStep P (instHost I) c₁ (some ev) c₂) :
    ∃ t', I.Trans P (.running a s t) (.inl (.ask x.1)) (.waiting a ev.1.2.1 t' x.1) ∧
      I.Trans P (.waiting a ev.1.2.1 t' x.1) (.inl (.ans x.1 x.2))
        (.running a c₂.store (.active c₂.frame c₂.code)) := by
  obtain ⟨e, v⟩ := x
  obtain ⟨⟨hh, s₀, us⟩, ⟨s₁, r⟩⟩ := ev
  obtain ⟨hop, hs₁, hr⟩ := hv
  simp only at hop hs₁ hr
  subst hs₁ hr
  obtain ⟨t', hreach, ht'⟩ := silent_reach h₁ rfl
  obtain ⟨E, a', hd, hst, -, rfl⟩ := h₂
  simp only at hd hst
  subst hst
  have hd' : decompose? c₁.store (t'.config c₁.store).code = some (E, a', hh, us) := by
    rw [ht']; exact hd
  have hres : resumeResult c₁.store t' (Answer.toResult v) =
      .active c₁.frame (E.fill (Answer.toResult v).toAdmin) := by
    unfold resumeResult
    simp only [hd']
    rw [ht']
  refine ⟨t', .ucall hreach ⟨E, a', hd'⟩ hop, ?_⟩
  have := ScalarInstance.Trans.uret (I := I) (P := P) (f := a) (s := c₁.store) (t := t') (e := e) v
  rw [hres] at this
  exact this

/-- **For each import call of a viewed log, the run passes through a waiting state at the store of
the Core event viewing it.** -/
theorem waiting_of_split {a : I.F.Op} :
    ∀ {c : List (Call I.E)} {cs : List (Call (wasmHostSig Nat))} {s : Store Nat} {t : Thread}
      {c' : Config Nat}, List.Forall₂ (CallView I) c cs → EvRunE P (instHost I) (t.config s) cs c' →
      ∀ c₁ x c₂, c = c₁ ++ x :: c₂ → ∃ ev t', ev ∈ cs ∧ CallView I x ev ∧
        I.Path P (.running a s t) (callMoves c₁ ++ [.inl (.ask x.1)]) (.waiting a ev.1.2.1 t' x.1)
  | [], [], _, _, _, .nil, _, c₁, x, c₂, h => by simp at h
  | y :: c, ev :: cs, s, t, c', .cons hv hF, hE, c₁, x, c₂, h => by
    obtain ⟨d₁, d₂, hsil, hev, hE'⟩ := hE
    obtain ⟨t', h₁, h₂⟩ := seg_bwd_waiting (a := a) hv hsil hev
    cases c₁ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨ev, t', List.mem_cons_self .., hv, .cons h₁ (.nil _)⟩
    | cons z c₁ =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨ev', t'', hm, hv', hp⟩ := waiting_of_split (a := a) (s := d₂.store)
        (t := .active d₂.frame d₂.code) hF hE' c₁ x c₂ h
      exact ⟨ev', t'', List.mem_cons_of_mem _ hm, hv', .cons h₁ (.cons h₂ hp)⟩

/-- **Each Core event of a viewed log is met at a waiting state at its store.** -/
theorem waiting_of_mem {a : I.F.Op} :
    ∀ {c : List (Call I.E)} {cs : List (Call (wasmHostSig Nat))} {s : Store Nat} {t : Thread}
      {c' : Config Nat}, List.Forall₂ (CallView I) c cs → EvRunE P (instHost I) (t.config s) cs c' →
      ∀ ev ∈ cs, ∃ c₁ x c₂ t', c = c₁ ++ x :: c₂ ∧ CallView I x ev ∧
        I.Path P (.running a s t) (callMoves c₁ ++ [.inl (.ask x.1)]) (.waiting a ev.1.2.1 t' x.1)
  | [], [], _, _, _, .nil, _, ev, hm => by simp at hm
  | y :: c, e :: cs, s, t, c', .cons hv hF, hE, ev, hm => by
    obtain ⟨d₁, d₂, hsil, hev, hE'⟩ := hE
    obtain ⟨t', h₁, h₂⟩ := seg_bwd_waiting (a := a) hv hsil hev
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨[], y, c, t', rfl, hv, .cons h₁ (.nil _)⟩
    · obtain ⟨c₁, x, c₂, t'', rfl, hv', hp⟩ := waiting_of_mem (a := a) (s := d₂.store)
        (t := .active d₂.frame d₂.code) hF hE' ev hm
      exact ⟨y :: c₁, x, c₂, t'', rfl, hv', .cons h₁ (.cons h₂ hp)⟩

/-- **Core-event legality of a witness is `RoundLegal` of the log it views** (deterministic
profile: the waiting state after a play is unique). -/
theorem coreLegal_iff {o : GrowOracle} {s : Store Nat} {a : I.F.Op} {c : List (Call I.E)}
    {cs : List (Call (wasmHostSig Nat))} {c' : Config Nat} (hF : List.Forall₂ (CallView I) c cs)
    (hE : EvRunE (profile o) (instHost I) (invoke s (qOf I a).1 (qOf I a).2) cs c') :
    (∀ ev ∈ cs, Q ev.1.2.1 ev.2.2) ↔ RoundLegal I (profile o) Q s a c := by
  constructor
  · intro hl c₁ x c₂ hc s' t hp
    obtain ⟨ev, t', hm, hv, hp'⟩ := waiting_of_split (a := a) (t := I.initThread a) hF hE c₁ x c₂ hc
    have hq := ScalarInstance.Path.functional hp
      (Proofs.Wasm.Abstract.NodeBridge.path_idle_ask_iff.2 hp')
    cases hq
    rw [← hv.2.2]
    exact hl ev hm
  · intro hR ev hm
    obtain ⟨c₁, x, c₂, t', hc, hv, hp⟩ := waiting_of_mem (a := a) (t := I.initThread a) hF hE ev hm
    rw [hv.2.2]
    exact hR c₁ x c₂ hc _ t' (Proofs.Wasm.Abstract.NodeBridge.path_idle_ask_iff.2 hp)

/-- Without determinism: `RoundLegal` of the viewed log gives Core-event legality. -/
theorem coreLegal_of_roundLegal {s : Store Nat} {a : I.F.Op} {c : List (Call I.E)}
    {cs : List (Call (wasmHostSig Nat))} {c' : Config Nat} (hF : List.Forall₂ (CallView I) c cs)
    (hE : EvRunE P (instHost I) (invoke s (qOf I a).1 (qOf I a).2) cs c')
    (hR : RoundLegal I P Q s a c) : ∀ ev ∈ cs, Q ev.1.2.1 ev.2.2 := by
  intro ev hm
  obtain ⟨c₁, x, c₂, t', hc, hv, hp⟩ := waiting_of_mem (a := a) (t := I.initThread a) hF hE ev hm
  rw [hv.2.2]
  exact hR c₁ x c₂ hc _ t' (Proofs.Wasm.Abstract.NodeBridge.path_idle_ask_iff.2 hp)

end Waiting

/-! ## Runs of the three kinds of observation -/

section Obs

theorem evRunE_of_evRun {c c' : Config Nat} {cs : List (Call (wasmHostSig Nat))}
    (h : EvRun P (instHost I) c cs c') : ∃ c'', EvRunE P (instHost I) c cs c'' := by
  obtain ⟨c'', h, -⟩ := evRun_iff.1 h
  exact ⟨c'', h⟩

theorem evRunE_of_fin {s : Store Nat} {q : Nat × List Val}
    {y : CallBeh (wasmHostSig Nat) (Store Nat) ((List Val ⊕ Nat) ⊕ PUnit)}
    (h : y ∈ (coreTripleSO P (instHost I)).1 s q) :
    ∃ c'', EvRunE P (instHost I) (invoke s q.1 q.2) y.1 c'' := by
  obtain ⟨cs, e⟩ := y
  obtain ⟨-, hb⟩ := h
  rcases e with ((ws | t) | u) | _ | _
  · exact evRunE_of_evRun (c' := ⟨_, {}, vals ws⟩) hb
  · exact evRunE_of_evRun (c' := ⟨_, {}, throwing t⟩) hb
  · exact evRunE_of_evRun (c' := ⟨_, {}, [.trap]⟩) hb
  · exact (show False from hb).elim
  · obtain ⟨c', hr, -⟩ := hb
    exact evRunE_of_evRun hr

theorem evRunE_of_pend {s : Store Nat} {q : Nat × List Val}
    {y : List (Call (wasmHostSig Nat)) × (wasmHostSig Nat).Op}
    (h : CoreCallout P (instHost I) s q y) :
    ∃ c'', EvRunE P (instHost I) (invoke s q.1 q.2) y.1 c'' := by
  obtain ⟨c, -, -, hr, -⟩ := h
  exact evRunE_of_evRun hr

theorem evRunE_snoc {c c' c'' : Config Nat} {cs : List (Call (wasmHostSig Nat))}
    {e : Call (wasmHostSig Nat)} (h : EvRunE P (instHost I) c cs c')
    (he : ∃ c₁, Relation.ReflTransGen (fun a b => HEvStep P (instHost I) a none b) c' c₁ ∧
      HEvStep P (instHost I) c₁ (some e) c'') :
    EvRunE P (instHost I) c (cs ++ [e]) c'' := by
  induction cs generalizing c with
  | nil =>
    obtain ⟨c₁, h₁, h₂⟩ := he
    have : c' = c := h
    subst this
    exact ⟨c₁, c'', h₁, h₂, rfl⟩
  | cons x cs ih =>
    obtain ⟨d₁, d₂, h₁, h₂, h₃⟩ := h
    exact ⟨d₁, d₂, h₁, h₂, ih h₃⟩

theorem evRunE_of_inf {c : Config Nat} {ω : ℕ → Call (wasmHostSig Nat)}
    (h : CoreInf P (instHost I) c ω) (k : ℕ) :
    ∃ c'', EvRunE P (instHost I) c (streamTake ω k) c'' := by
  obtain ⟨g, hg0, hg⟩ := h
  suffices ∀ k, EvRunE P (instHost I) c (streamTake ω k) (g k) from ⟨_, this k⟩
  intro k
  induction k with
  | zero => exact hg0
  | succ k ih =>
    rw [Games.Abstract.SessionLegal.streamTake_succ]
    exact evRunE_snoc ih (hg k)

theorem forall₂_streamTake {α β : Type} {R : α → β → Prop} {ω : ℕ → α} {ω' : ℕ → β}
    (h : ∀ k, R (ω k) (ω' k)) (k : ℕ) : List.Forall₂ R (streamTake ω k) (streamTake ω' k) := by
  induction k with
  | zero => exact .nil
  | succ k ih =>
    rw [Games.Abstract.SessionLegal.streamTake_succ,
      Games.Abstract.SessionLegal.streamTake_succ]
    exact List.rel_append ih (.cons (h k) .nil)

theorem mem_streamTake {α : Type} {ω : ℕ → α} {k : ℕ} {x : α} (h : x ∈ streamTake ω k) :
    ∃ j, x = ω j := by
  simp only [streamTake, List.mem_ofFn] at h
  obtain ⟨j, rfl⟩ := h
  exact ⟨j, rfl⟩

theorem mem_streamTake_succ {α : Type} (ω : ℕ → α) (k : ℕ) : ω k ∈ streamTake ω (k + 1) := by
  rw [Games.Abstract.SessionLegal.streamTake_succ]
  simp

end Obs

/-! ## The restricted instance triple -/

section Triple

variable {o : GrowOracle}

theorem roundLegal_prefixClosed : SessionLegal.PrefixClosed (RoundLegal I P Q) := by
  intro s a c d h c₁ x c₂ hc
  exact h c₁ x (c₂ ++ d) (by rw [hc]; simp)

theorem mem_fin_iff {s : Store Nat} {a : I.F.Op}
    {x : CallBeh I.E (Store Nat) (Res I.exports ⊕ PUnit)} :
    x ∈ (instTripleQ I (profile o) Q).1 s a ↔
      x ∈ (instTripleS I (profile o)).1 s a ∧ RoundLegal I (profile o) Q s a x.1 := by
  rw [NodeBridge.instTripleS_eq_viewTriple]
  constructor
  · rintro ⟨y, ⟨hy, hl⟩, hF, hv⟩
    obtain ⟨c'', hE⟩ := evRunE_of_fin hy
    exact ⟨⟨y, hy, hF, hv⟩, (coreLegal_iff hF hE).1 hl⟩
  · rintro ⟨⟨y, hy, hF, hv⟩, hR⟩
    obtain ⟨c'', hE⟩ := evRunE_of_fin hy
    exact ⟨y, ⟨hy, (coreLegal_iff hF hE).2 hR⟩, hF, hv⟩

theorem mem_pend_iff {s : Store Nat} {a : I.F.Op} {x : List (Call I.E) × I.E.Op} :
    x ∈ (instTripleQ I (profile o) Q).2.1 s a ↔
      x ∈ (instTripleS I (profile o)).2.1 s a ∧ RoundLegal I (profile o) Q s a x.1 := by
  rw [NodeBridge.instTripleS_eq_viewTriple]
  constructor
  · rintro ⟨y, ⟨hy, hl⟩, hF, hv⟩
    obtain ⟨c'', hE⟩ := evRunE_of_pend hy
    exact ⟨⟨y, hy, hF, hv⟩, (coreLegal_iff hF hE).1 hl⟩
  · rintro ⟨⟨y, hy, hF, hv⟩, hR⟩
    obtain ⟨c'', hE⟩ := evRunE_of_pend hy
    exact ⟨y, ⟨hy, (coreLegal_iff hF hE).2 hR⟩, hF, hv⟩

theorem mem_inf_iff {s : Store Nat} {a : I.F.Op} {ω : ℕ → Call I.E} :
    ω ∈ (instTripleQ I (profile o) Q).2.2 s a ↔
      ω ∈ (instTripleS I (profile o)).2.2 s a ∧
        ∀ k, RoundLegal I (profile o) Q s a (streamTake ω k) := by
  rw [NodeBridge.instTripleS_eq_viewTriple]
  constructor
  · rintro ⟨ω', ⟨hy, hl⟩, hv⟩
    refine ⟨⟨ω', hy, hv⟩, fun k => ?_⟩
    obtain ⟨c'', hE⟩ := evRunE_of_inf hy.2 k
    refine (coreLegal_iff (forall₂_streamTake hv k) hE).1 fun ev hm => ?_
    obtain ⟨j, rfl⟩ := mem_streamTake hm
    exact hl j
  · rintro ⟨⟨ω', hy, hv⟩, hR⟩
    refine ⟨ω', ⟨hy, fun k => ?_⟩, hv⟩
    obtain ⟨c'', hE⟩ := evRunE_of_inf hy.2 (k + 1)
    exact (coreLegal_iff (forall₂_streamTake hv (k + 1)) hE).2 (hR (k + 1)) _
      (mem_streamTake_succ ω' k)

/-- The call prefixes of a relabelled triple are those of the triple. -/
theorem satP_mapAns {E : Sig.{0}} {S A B B' : Type} (g : B → B') (t : ObsTriple E S A B) :
    satP (InstSession.mapAns g t) = satP t := by
  funext s a
  ext x
  constructor
  · rintro (h | h | ⟨d, e, ⟨y, hy, he⟩, hp⟩ | h)
    · exact .inl h
    · exact .inr (.inl h)
    · cases he; exact .inr (.inr (.inl ⟨_, _, hy, hp⟩))
    · exact .inr (.inr (.inr h))
  · rintro (h | h | ⟨d, e, hy, hp⟩ | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl ⟨d, _, ⟨(d, e), hy, rfl⟩, hp⟩))
    · exact .inr (.inr (.inr h))

/-- **The instance triple is saturated**: its call prefixes are its pending calls. -/
theorem satP_instTripleS_sub {s : Store Nat} {a : I.F.Op} {x : List (Call I.E) × I.E.Op}
    (h : x ∈ satP (instTripleS I P) s a) : x ∈ (instTripleS I P).2.1 s a := by
  obtain ⟨c, m⟩ := x
  rw [InstSession.instTripleS_eq, satP_mapAns] at h
  exact Proofs.Wasm.Abstract.InstStrat.satP_sound h

theorem satP_mono {E : Sig.{0}} {S A B : Type} {t t' : ObsTriple E S A B} {s : S} {a : A}
    (h₁ : t.1 s a ⊆ t'.1 s a) (h₂ : t.2.1 s a ⊆ satP t' s a) (h₃ : t.2.2 s a ⊆ t'.2.2 s a)
    {x : List (Call E) × E.Op} (h : x ∈ satP t s a) : x ∈ satP t' s a := by
  rcases h with h | ⟨d, m', hd, hp⟩ | ⟨d, e, hd, hp⟩ | ⟨ω, hω, k, hk, hm⟩
  · exact h₂ h
  · exact Games.Abstract.SessionLegal.satP_of_callPre (h₂ hd) hp
  · exact .inr (.inr (.inl ⟨d, e, h₁ hd, hp⟩))
  · exact .inr (.inr (.inr ⟨ω, h₃ hω, k, hk, hm⟩))

theorem satP_iff {s : Store Nat} {a : I.F.Op} {x : List (Call I.E) × I.E.Op} :
    x ∈ satP (instTripleQ I (profile o) Q) s a ↔
      x ∈ satP (instTripleS I (profile o)) s a ∧ RoundLegal I (profile o) Q s a x.1 := by
  have hset := Games.Abstract.SessionLegal.satP_restrictLog
    (t := instTripleS I (profile o)) (roundLegal_prefixClosed (I := I) (P := profile o) (Q := Q)) s a
  constructor
  · intro h
    have h' : x ∈ satP (SessionLegal.restrictLog (RoundLegal I (profile o) Q)
        (instTripleS I (profile o))) s a :=
      satP_mono (t' := SessionLegal.restrictLog (RoundLegal I (profile o) Q)
          (instTripleS I (profile o))) (fun y hy => mem_fin_iff.1 hy)
        (fun y hy => .inl ⟨.inl (mem_pend_iff.1 hy).1, (mem_pend_iff.1 hy).2⟩)
        (fun ω hω => mem_inf_iff.1 hω) h
    rw [hset] at h'
    exact h'
  · rintro ⟨h, hR⟩
    exact .inl (mem_pend_iff.2 ⟨satP_instTripleS_sub h, hR⟩)

/-- **The restricted instance triple is the legal part of the instance triple**, at every store:
same finished behaviours, call prefixes and productive streams. -/
theorem agree (s : Store Nat) :
    (instTripleQ I (profile o) Q).1 s =
        (SessionLegal.restrictLog (RoundLegal I (profile o) Q) (instTripleS I (profile o))).1 s ∧
      satP (instTripleQ I (profile o) Q) s =
        satP (SessionLegal.restrictLog (RoundLegal I (profile o) Q) (instTripleS I (profile o))) s ∧
      (instTripleQ I (profile o) Q).2.2 s =
        (SessionLegal.restrictLog (RoundLegal I (profile o) Q) (instTripleS I (profile o))).2.2 s := by
  refine ⟨funext fun a => Set.ext fun x => mem_fin_iff, funext fun a => ?_,
    funext fun a => Set.ext fun ω => mem_inf_iff⟩
  rw [Games.Abstract.SessionLegal.satP_restrictLog roundLegal_prefixClosed]
  exact Set.ext fun x => satP_iff

theorem threadS_eq (s₀ : Store Nat) :
    StratSession.threadS (instTripleQ I (profile o) Q) s₀ =
      StratSession.threadS
        (SessionLegal.restrictLog (RoundLegal I (profile o) Q) (instTripleS I (profile o))) s₀ :=
  StratSession.threadS_congr fun s _ => agree s

end Triple

end Silmaril.Proofs.Wasm.Abstract.NodeLegal
