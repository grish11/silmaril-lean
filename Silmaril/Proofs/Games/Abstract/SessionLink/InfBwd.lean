module

public import Silmaril.Proofs.Games.Abstract.SessionLink.Div
import Mathlib.Data.List.Basic

/-!
# Linking sessions: infinite plays, backward direction (proofs)

Every infinite play of the linked session is an infinite play of the composite, when the linked
triple is store-deterministic (`inf_bwd`):

* a stream after completed linked rounds is the limit of an interaction in which the server
  streams inside a served call, or the client streams with its calls served;
* a coherent infinite sequence of linked rounds (`StratThread.InfRounds`) is the limit of the
  concatenated interactions of its rounds.

Store determinism of the linked triple is what makes the linked rounds coherent: the hidden
interaction of each linked round must extend the hidden interaction of the previous ones.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLink

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionLink

universe u

variable {E : Sig.{u}} {S S' A B A' B' : Type u} {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

theorem zip_length_le {α β γ : Type u} {s : List (α ⊕ β)} {t : List (β ⊕ γ)}
    {p : List (α ⊕ γ)} (h : Zip s t p) : p.length ≤ s.length + t.length := by
  induction h with
  | nil => simp
  | left _ _ ih => simp; omega
  | right _ _ ih => simp; omega
  | sync _ _ ih => simp; omega

/-- A constant chain is bounded. -/
theorem not_unbounded_const {α : Type u} {l : List α} :
    ¬ Chain.Unbounded (fun _ => l : Chain α) := fun h => by
  obtain ⟨n, hn⟩ := h (l.length + 1)
  simp at hn; omega

/-- The stream play of a stream approximated by increasing call lists. -/
theorem lim_eq_streamPlay {F : Sig.{u}} {A₁ : Type u} (pre : List (Move F (sig1 A₁ B')))
    (a : A₁) (ω : ℕ → Call F) (c : ℕ → List (Call F))
    (hc : ∀ k, streamTake ω (c k).length = c k) (hun : ∀ n, ∃ k, n ≤ (c k).length) :
    Chain.lim (fun k => pre ++ .inr (.ask a) :: callMoves (c k)) = streamPlay pre a ω := by
  ext q
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨_, by rw [hc k]; exact hk⟩
  · rintro ⟨j, hj⟩
    obtain ⟨k, hk⟩ := hun j
    refine ⟨k, hj.trans ?_⟩
    refine (List.prefix_append_right_inj _).2 (List.cons_prefix_cons.2 ⟨rfl, ?_⟩)
    rw [← hc k]
    exact callMoves_prefix (streamTake_prefix ω hk)

/-- **A stream after completed linked rounds is an infinite play of the composite.** -/
theorem inf_bwd_stream {s₀ : S} {s₀' : S'}
    {rsL : List (A' × List (Call E) × (B' ⊕ PUnit.{u + 1}))} {σ : S × S'} {a' : A'}
    {ω : ℕ → Call E} (hrsL : Rounds (linkS t u) (s₀, s₀') rsL σ)
    (hω : ω ∈ (linkS t u).2.2 σ a') :
    streamPlay (sroundsMoves rsL) a' ω ∈ ((threadS t s₀).comp (threadS u s₀')).inf := by
  obtain ⟨sv₀, cv₀, hz₀, hv₀, hc₀⟩ := bwd_rounds hrsL
  rcases hω with ⟨rs, s₁, a, ω', hR, hu, hω', hk⟩ | ⟨ω', hω', l, st, hs, hun, hk⟩
  · -- the server streams inside a served call
    obtain ⟨hz, hv, hc⟩ := core_run (a' := a') hR hu (c₁ := []) (fun _ _ h => by
      obtain ⟨_, _, h⟩ := h; simp at h)
    have hz' : ∀ k, Zip (sv₀ ++ (sroundsMoves rs ++ .inr (.ask a) :: callMoves (streamTake ω' k)))
        (cv₀ ++ .inr (.ask a') :: (callMoves (served rs) ++ [.inl (.ask a)]))
        (sroundsMoves rsL ++ .inr (.ask a') :: callMoves (servedLog rs ++ streamTake ω' k)) :=
      fun k => by
        have := zip_append (zip_append hz₀ hz) (zip_callMoves_left (F := sig1 A B)
          (G := sig1 A' B') (streamTake ω' k))
        simpa using this
    have hvk : ∀ k, SRun t (.idle s₀)
        (sv₀ ++ (sroundsMoves rs ++ .inr (.ask a) :: callMoves (streamTake ω' k)))
        (.run s₁ a (streamTake ω' k)) := fun k => by
      have h := run_callMoves (t := t) (s := s₁) (a := a) (streamTake ω' k) (c₀ := [])
        (fun c m hc => by
          obtain ⟨j, rfl, rfl⟩ := callPre_streamTake (by simpa using hc)
          exact .inr (.inr (.inr ⟨ω', hω', j, rfl, rfl⟩)))
      simp only [List.nil_append] at h
      have := hv₀.append (hv.append h)
      simpa using this
    have mono_s : Chain.Mono fun k =>
        sv₀ ++ (sroundsMoves rs ++ .inr (.ask a) :: callMoves (streamTake ω' k)) := fun k =>
      (List.prefix_append_right_inj _).2 ((List.prefix_append_right_inj _).2
        (List.cons_prefix_cons.2 ⟨rfl, callMoves_prefix (streamTake_prefix ω' (by omega))⟩))
    have mono_p : Chain.Mono fun k =>
        sroundsMoves rsL ++ .inr (.ask a') :: callMoves (servedLog rs ++ streamTake ω' k) :=
      fun k => (List.prefix_append_right_inj _).2 (List.cons_prefix_cons.2 ⟨rfl,
        callMoves_prefix ((List.prefix_append_right_inj _).2 (streamTake_prefix ω' (by omega)))⟩)
    have hpu : Chain.Unbounded fun k =>
        sroundsMoves rsL ++ .inr (.ask a') :: callMoves (servedLog rs ++ streamTake ω' k) :=
      fun j => ⟨j, by simp [length_callMoves]; omega⟩
    let i : DStrategy.InfInteraction (threadS t s₀) (threadS u s₀') :=
      { s := fun k => sv₀ ++ (sroundsMoves rs ++ .inr (.ask a) :: callMoves (streamTake ω' k))
        t := fun _ => cv₀ ++ .inr (.ask a') :: (callMoves (served rs) ++ [.inl (.ask a)])
        p := fun k => sroundsMoves rsL ++ .inr (.ask a') ::
          callMoves (servedLog rs ++ streamTake ω' k)
        zip := hz'
        mem_s := fun k => mem_plays.2 ⟨_, hvk k⟩
        mem_t := fun _ => mem_plays.2 ⟨_, hc₀.append hc⟩
        mono_s := mono_s
        mono_t := fun _ => List.prefix_refl _
        mono_p := mono_p
        unbounded := fun j => ⟨j, by simp [length_callMoves]; omega⟩
        lim_s := fun _ => by
          have h := lim_streamPlay (sv₀ ++ sroundsMoves rs) a ω' 0
          simp only [Nat.zero_add, List.append_assoc] at h
          show Chain.lim _ ∈ _
          rw [h]
          exact mem_inf_of_stream (hv₀.append (run_rounds hR)) hω'
        lim_t := fun hu => absurd hu not_unbounded_const }
    refine ⟨i, hpu, ?_⟩
    show _ = Chain.lim fun k => sroundsMoves rsL ++ .inr (.ask a') ::
      callMoves (servedLog rs ++ streamTake ω' k)
    rw [lim_eq_streamPlay _ a' ω (fun k => servedLog rs ++ streamTake ω' k)
      (fun k => by simpa using hk k) (fun j => ⟨j, by simp⟩)]
  · -- the client streams, its calls served, with infinitely many server calls
    let sv : Chain (Move E (sig1 A B)) := fun k =>
      sv₀ ++ sroundsMoves (streamTake (serveRounds ω' l) k)
    let cv : Chain (Move (sig1 A B) (sig1 A' B')) := fun k =>
      cv₀ ++ .inr (.ask a') :: callMoves (streamTake ω' k)
    have hzk : ∀ k, Zip (sv k) (cv k) (sroundsMoves rsL ++ .inr (.ask a') ::
        callMoves (logTake l k)) := fun k => by
      have h := zip_append hz₀ (Zip.right (.ask a') (zip_served (G := sig1 A' B')
        (streamTake (serveRounds ω' l) k)))
      rwa [served_serveRounds, servedLog_serveRounds] at h
    have hvk : ∀ k, SRun t (.idle s₀) (sv k) (.idle (st k)) := fun k =>
      hv₀.append (run_rounds (infServe_rounds hs k))
    have hck : ∀ k, SRun u (.idle s₀') (cv k) (.run σ.2 a' (streamTake ω' k)) := fun k => by
      refine hc₀.append (.cons (.ask _ _) ?_)
      simpa using run_callMoves (t := u) (s := σ.2) (a := a') (streamTake ω' k) (c₀ := [])
        (by simpa using auth_of_stream hω' k)
    have mono_s : sv.Mono := fun k => by
      refine (List.prefix_append_right_inj _).2 ?_
      rw [streamTake_succ, sroundsMoves_append]
      exact List.prefix_append _ _
    have mono_t : cv.Mono := fun k =>
      (List.prefix_append_right_inj _).2 (List.cons_prefix_cons.2 ⟨rfl,
        callMoves_prefix (streamTake_prefix ω' (by omega))⟩)
    have mono_p : Chain.Mono fun k =>
        sroundsMoves rsL ++ .inr (.ask a') :: callMoves (logTake l k) := fun k =>
      (List.prefix_append_right_inj _).2 (List.cons_prefix_cons.2 ⟨rfl,
        callMoves_prefix (by rw [logTake_succ]; exact List.prefix_append _ _)⟩)
    have hpu : Chain.Unbounded fun k =>
        sroundsMoves rsL ++ .inr (.ask a') :: callMoves (logTake l k) := fun j => by
      obtain ⟨k, hk⟩ := hun j
      exact ⟨k, by simp [length_callMoves]; omega⟩
    let i : DStrategy.InfInteraction (threadS t s₀) (threadS u s₀') :=
      { s := sv
        t := cv
        p := fun k => sroundsMoves rsL ++ .inr (.ask a') :: callMoves (logTake l k)
        zip := hzk
        mem_s := fun k => mem_plays.2 ⟨_, hvk k⟩
        mem_t := fun k => mem_plays.2 ⟨_, hck k⟩
        mono_s := mono_s
        mono_t := mono_t
        mono_p := mono_p
        unbounded := fun k => ⟨k, by
          simp only [cv, List.length_append, List.length_cons, length_callMoves,
            length_streamTake]
          omega⟩
        lim_s := fun hu => mem_inf_of_idle mono_s hu fun k => ⟨_, hvk k⟩
        lim_t := fun _ => by
          have h := lim_streamPlay cv₀ a' ω' 0
          simp only [Nat.zero_add] at h
          show Chain.lim cv ∈ _
          rw [show cv = fun k => cv₀ ++ .inr (.ask a') :: callMoves (streamTake ω' k) from rfl, h]
          exact mem_inf_of_stream hc₀ hω' }
    exact ⟨i, hpu, (lim_eq_streamPlay _ a' ω (logTake l) hk hun).symm⟩

/-- **A coherent infinite sequence of linked rounds is an infinite play of the composite.** -/
theorem inf_bwd_rounds {s₀ : S} {s₀' : S'} {a : ℕ → A'}
    {r : ℕ → List (Call E) × (B' ⊕ PUnit.{u + 1})} {st : ℕ → S × S'}
    (h : InfRounds (linkS t u) (s₀, s₀') a r st) :
    sroundsPlay a r ∈ ((threadS t s₀).comp (threadS u s₀')).inf := by
  have hround : ∀ k, ∃ sv cv, Zip sv cv (sroundMoves (a k, (r k).1, (r k).2)) ∧
      SRun t (.idle (st k).1) sv (.idle (st (k + 1)).1) ∧
      SRun u (.idle (st k).2) cv (.idle (st (k + 1)).2) := fun k => bwd_round (h.step k)
  choose SV CV hZ hV hC using hround
  let sv : Chain (Move E (sig1 A B)) := fun n => (streamTake SV n).flatten
  let cv : Chain (Move (sig1 A B) (sig1 A' B')) := fun n => (streamTake CV n).flatten
  let pv : Chain (Move E (sig1 A' B')) := fun n => sroundsMoves (streamTake (fun i => (a i, r i)) n)
  have hz : ∀ n, Zip (sv n) (cv n) (pv n) := fun n => by
    induction n with
    | zero => exact .nil
    | succ n ih =>
      simp only [sv, cv, pv, streamTake_succ, List.flatten_append, List.flatten_singleton,
        sroundsMoves_append, sroundsMoves_cons, sroundsMoves_nil, List.append_nil] at ih ⊢
      exact zip_append ih (hZ n)
  have h0 : st 0 = (s₀, s₀') := h.zero
  have hv : ∀ n, SRun t (.idle s₀) (sv n) (.idle (st n).1) := fun n => by
    induction n with
    | zero => rw [h0]; exact .nil _
    | succ n ih =>
      simp only [sv, streamTake_succ, List.flatten_append, List.flatten_singleton] at ih ⊢
      exact ih.append (hV n)
  have hc : ∀ n, SRun u (.idle s₀') (cv n) (.idle (st n).2) := fun n => by
    induction n with
    | zero => rw [h0]; exact .nil _
    | succ n ih =>
      simp only [cv, streamTake_succ, List.flatten_append, List.flatten_singleton] at ih ⊢
      exact ih.append (hC n)
  have mono_s : sv.Mono := fun n => by
    simp only [sv, streamTake_succ, List.flatten_append]; exact List.prefix_append _ _
  have mono_t : cv.Mono := fun n => by
    simp only [cv, streamTake_succ, List.flatten_append]; exact List.prefix_append _ _
  have mono_p : pv.Mono := fun n => by
    simp only [pv, streamTake_succ, sroundsMoves_append]; exact List.prefix_append _ _
  have hlen : ∀ n, 2 * n ≤ (pv n).length := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pv, streamTake_succ, sroundsMoves_append, List.length_append] at ih ⊢
      simp [sroundMoves]; omega
  let i : DStrategy.InfInteraction (threadS t s₀) (threadS u s₀') :=
    { s := sv
      t := cv
      p := pv
      zip := hz
      mem_s := fun n => mem_plays.2 ⟨_, hv n⟩
      mem_t := fun n => mem_plays.2 ⟨_, hc n⟩
      mono_s := mono_s
      mono_t := mono_t
      mono_p := mono_p
      unbounded := fun k => ⟨k, by
        show k ≤ (sv k).length + (cv k).length
        have := hlen k; have := zip_length_le (hz k); omega⟩
      lim_s := fun hu => mem_inf_of_idle mono_s hu fun n => ⟨_, hv n⟩
      lim_t := fun hu => mem_inf_of_idle mono_t hu fun n => ⟨_, hc n⟩ }
  exact ⟨i, fun k => ⟨k, by show k ≤ (pv k).length; have := hlen k; omega⟩, rfl⟩

/-- **Backward**: for a store-deterministic linked triple, every infinite play of the linked
session is an infinite play of the composite. -/
theorem inf_bwd (hL : StoreDet (linkS t u)) {s₀ : S} {s₀' : S'}
    {I : Set (List (Move E (sig1 A' B')))} (hI : I ∈ (threadS (linkS t u) (s₀, s₀')).inf) :
    I ∈ ((threadS t s₀).comp (threadS u s₀')).inf := by
  rcases (StratSession.mem_inf_iff_of_storeDet hL).1 hI with ⟨rs, σ, a', ω, hrs, hω, rfl⟩ |
      ⟨a, r, st, h, rfl⟩
  · exact inf_bwd_stream hrs hω
  · exact inf_bwd_rounds h

end Silmaril.Proofs.Games.Abstract.SessionLink
