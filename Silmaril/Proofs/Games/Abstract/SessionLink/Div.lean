module

public import Silmaril.Proofs.Games.Abstract.SessionLink.Plays
public import Silmaril.Games.DivComp.Thms
import Mathlib.Data.List.Basic

/-!
# Linking sessions: divergence (proofs)

* `div_bwd`: every divergence of the linked session is a divergence of the composite: a client
  divergence or a server divergence inside a served call is a local divergence of one component;
  a served client stream with finitely many server calls is an infinite interaction whose visible
  part is constant (hidden chatter);
* `div_fwd_local`: a local divergence of the composite (one component diverges) is a divergence
  of the linked session.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLink

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionLink

universe u

variable {E : Sig.{u}} {S S' A B A' B' : Type u} {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

theorem callMoves_prefix {F : Sig.{u}} {c d : List (Call E)} (h : c <+: d) :
    (callMoves c : List (Move E F)) <+: callMoves d := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨callMoves r, by simp⟩

/-- The stream play of a prefix and a stream is the limit of its stream prefixes from `n` on. -/
theorem lim_streamPlay {F : Sig.{u}} {A₁ : Type u} (pre : List (Move F (sig1 A₁ B')))
    (a : A₁) (ω : ℕ → Call F) (n : ℕ) :
    Chain.lim (fun k => pre ++ .inr (.ask a) :: callMoves (streamTake ω (n + k))) =
      streamPlay pre a ω := by
  ext q
  constructor
  · rintro ⟨k, hk⟩; exact ⟨n + k, hk⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, hk.trans ?_⟩
    refine (List.prefix_append_right_inj _).2 (List.cons_prefix_cons.2 ⟨rfl, ?_⟩)
    exact callMoves_prefix (streamTake_prefix ω (by omega))

/-- An infinite play whose stages all end idle completes infinitely many rounds. -/
theorem mem_inf_of_idle {s₀ : S} {c : Chain (Move E (sig1 A B))} (hm : c.Mono)
    (hu : c.Unbounded) (h : ∀ n, ∃ s, SRun t (.idle s₀) (c n) (.idle s)) :
    c.lim ∈ (threadS t s₀).inf :=
  mem_inf_of_rounds (Chain.isInfPlay_lim hm hu) fun _ ⟨n, hq⟩ =>
    ⟨c n, Chain.mem_lim_self c n, hq, h n⟩

/-- **Backward**: a divergence of the linked session is a divergence of the composite. -/
theorem div_bwd {s₀ : S} {s₀' : S'} {p : List (Move E (sig1 A' B'))}
    (hp : p ∈ (threadS (linkS t u) (s₀, s₀')).div) :
    p ∈ ((threadS t s₀).comp (threadS u s₀')).div := by
  obtain ⟨σ, a', c, hrun, hd⟩ := mem_div.1 hp
  obtain ⟨rsL, hrsL, rfl, -⟩ := shape hrun
  obtain ⟨sv₀, cv₀, hz₀, hv₀, hc₀⟩ := bwd_rounds hrsL
  rcases hd with ⟨rs, s₁, e, hR, hb, he⟩ | ⟨rs, s₁, a, c₁, hR, hu, hd, he⟩ |
      ⟨ω, hω, l, st, n, hs, hl, he⟩
  · -- the client diverges
    obtain ⟨rfl, he⟩ := Prod.ext_iff.1 he
    have he : e = .div := by cases e <;> simp_all [linkEnd]
    subst he
    obtain ⟨hz, hv, hc⟩ := core_served (a' := a') hR (fun _ _ h => satP_of_beh hb h)
    exact .inl ⟨_, _, zip_append hz₀ hz, .inr ⟨mem_plays.2 ⟨_, hv₀.append hv⟩,
      mem_div.2 ⟨_, _, _, hc₀.append hc, hb⟩⟩⟩
  · -- the server diverges inside a served call
    obtain ⟨rfl, -⟩ := Prod.ext_iff.1 he
    obtain ⟨hz, hv, hc⟩ := core_run hR hu (fun _ _ h => satP_of_beh hd h)
    exact .inl ⟨_, _, zip_append hz₀ hz, .inl ⟨mem_div.2 ⟨_, _, _, hv₀.append hv, hd⟩,
      mem_plays.2 ⟨_, hc₀.append hc⟩⟩⟩
  · -- hidden chatter: the client's stream, served, with finitely many server calls
    obtain ⟨rfl, -⟩ := Prod.ext_iff.1 he
    have hlog : ∀ k, logTake l (n + k) = logTake l n := fun k => by
      induction k with
      | zero => rfl
      | succ k ih => rw [← Nat.add_assoc, logTake_succ, ih, hl _ (by omega), List.append_nil]
    let sv : Chain (Move E (sig1 A B)) := fun k =>
      sv₀ ++ sroundsMoves (streamTake (serveRounds ω l) (n + k))
    let cv : Chain (Move (sig1 A B) (sig1 A' B')) := fun k =>
      cv₀ ++ .inr (.ask a') :: callMoves (streamTake ω (n + k))
    have hzk : ∀ k, Zip (sv k) (cv k) (sroundsMoves rsL ++ .inr (.ask a') ::
        callMoves (logTake l n)) := fun k => by
      have h := zip_append hz₀ (Zip.right (.ask a') (zip_served (G := sig1 A' B')
        (streamTake (serveRounds ω l) (n + k))))
      rwa [served_serveRounds, servedLog_serveRounds, hlog] at h
    have hvk : ∀ k, SRun t (.idle s₀) (sv k) (.idle (st (n + k))) := fun k =>
      hv₀.append (run_rounds (infServe_rounds hs (n + k)))
    have hck : ∀ k, SRun u (.idle s₀') (cv k) (.run σ.2 a' (streamTake ω (n + k))) := fun k => by
      refine hc₀.append (.cons (.ask _ _) ?_)
      simpa using run_callMoves (t := u) (s := σ.2) (a := a') (streamTake ω (n + k)) (c₀ := [])
        (by simpa using auth_of_stream hω (n + k))
    have mono_s : sv.Mono := fun k => by
      refine (List.prefix_append_right_inj _).2 ?_
      rw [← Nat.add_assoc, streamTake_succ, sroundsMoves_append]
      exact List.prefix_append _ _
    have mono_t : cv.Mono := fun k =>
      (List.prefix_append_right_inj _).2 (List.cons_prefix_cons.2 ⟨rfl,
        callMoves_prefix (streamTake_prefix ω (by omega))⟩)
    let i : DStrategy.InfInteraction (threadS t s₀) (threadS u s₀') :=
      { s := sv
        t := cv
        p := fun _ => sroundsMoves rsL ++ .inr (.ask a') :: callMoves (logTake l n)
        zip := hzk
        mem_s := fun k => mem_plays.2 ⟨_, hvk k⟩
        mem_t := fun k => mem_plays.2 ⟨_, hck k⟩
        mono_s := mono_s
        mono_t := mono_t
        mono_p := fun _ => List.prefix_refl _
        unbounded := fun k => ⟨k, by
          simp only [cv, List.length_append, List.length_cons, length_callMoves,
            length_streamTake]
          omega⟩
        lim_s := fun hu => mem_inf_of_idle mono_s hu fun k => ⟨_, hvk k⟩
        lim_t := fun _ => by
          show Chain.lim (fun k => cv₀ ++ .inr (.ask a') :: callMoves (streamTake ω (n + k))) ∈ _
          rw [lim_streamPlay]
          exact mem_inf_of_stream hc₀ hω }
    exact .inr ⟨i, fun _ => rfl⟩

/-- **Forward, local divergence**: an interaction in which one component diverges is a
divergence of the linked session. -/
theorem div_fwd_local (hnt : NoPlainTrap t) {s₀ : S} {s₀' : S'}
    {sv : List (Move E (sig1 A B))} {cv : List (Move (sig1 A B) (sig1 A' B'))}
    {p : List (Move E (sig1 A' B'))} (hz : Zip sv cv p)
    (h : (sv ∈ (threadS t s₀).div ∧ cv ∈ (threadS u s₀').toStrategy) ∨
      (sv ∈ (threadS t s₀).toStrategy ∧ cv ∈ (threadS u s₀').div)) :
    p ∈ (threadS (linkS t u) (s₀, s₀')).div := by
  rcases h with ⟨hsv, hcv⟩ | ⟨hsv, hcv⟩
  · obtain ⟨s, a, c, hx, hd⟩ := mem_div.1 hsv
    obtain ⟨y, hy⟩ := mem_plays.1 hcv
    obtain ⟨z, hzr, hJ⟩ := fwd hnt hz (J.idle s₀ s₀') hx hy
    cases hJ with
    | call σ a' rs _ _ _ hR hu =>
      exact mem_div.2 ⟨σ, a', _, hzr, .inr (.inl ⟨rs, s, a, c, hR, hu, hd, rfl⟩)⟩
  · obtain ⟨x, hx⟩ := mem_plays.1 hsv
    obtain ⟨s', a', d, hy, hd⟩ := mem_div.1 hcv
    obtain ⟨z, hzr, hJ⟩ := fwd hnt hz (J.idle s₀ s₀') hx hy
    cases hJ with
    | run σ _ rs s hR =>
      exact mem_div.2 ⟨σ, a', _, hzr, .inl ⟨rs, s, .div, hR, hd, rfl⟩⟩

end Silmaril.Proofs.Games.Abstract.SessionLink
