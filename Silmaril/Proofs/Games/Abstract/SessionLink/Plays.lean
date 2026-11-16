module

public import Silmaril.Proofs.Games.Abstract.SessionLink.Run
public import Silmaril.Games.DivComp.Defs
import Mathlib.Data.List.Basic

/-!
# Linking sessions: finite plays (proofs)

* `satP_linkS`: the call prefixes of the linked triple are its pending calls: every call forced
  by a linked behaviour or stream is a call prefix of the server inside a served call;
* `fwd`: an interaction of a server play and a client play has a visible part accepted by the
  linked session automaton, the three states related by `J`;
* `bwd_play`: conversely, a run of the linked session automaton is the visible part of an
  interaction (built from completed linked rounds and the current partial round);
* `mem_comp_iff`: the finite plays of the composite are those of the linked session.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLink

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionLink

universe u

variable {E : Sig.{u}} {S S' A B A' B' : Type u}

/-! ## Streams and call prefixes -/

section Streams

theorem take_streamTake {α : Type u} (ω : ℕ → α) {j k : ℕ} (h : j ≤ k) :
    (streamTake ω k).take j = streamTake ω j :=
  ((List.prefix_iff_eq_take.1 (streamTake_prefix ω h)).trans (by simp)).symm

theorem getElem_streamTake {α : Type u} (ω : ℕ → α) {j k : ℕ} (h : j < k) :
    (streamTake ω k)[j]'(by simpa using h) = ω j := by
  simp [streamTake]

/-- A list followed by an element inside a stream prefix is a stream prefix. -/
theorem streamTake_eq_append {α : Type u} {ω : ℕ → α} {k : ℕ} {c r : List α} {x : α}
    (h : streamTake ω k = c ++ x :: r) : streamTake ω c.length = c ∧ ω c.length = x := by
  have hk : c.length < k := by
    have := congrArg List.length h; simp at this; omega
  refine ⟨?_, ?_⟩
  · rw [← take_streamTake ω hk.le, h]; simp
  · rw [← getElem_streamTake ω hk]; simp [h]

theorem callPre_streamTake {E : Sig.{u}} {ω : ℕ → Call E} {k : ℕ}
    {c : List (Call E)} {m : E.Op} (h : CallPre c m (streamTake ω k)) :
    ∃ j, streamTake ω j = c ∧ (ω j).1 = m := by
  obtain ⟨n, r, hr⟩ := h
  obtain ⟨h₁, h₂⟩ := streamTake_eq_append hr
  exact ⟨c.length, h₁, by rw [h₂]⟩

theorem callPre_of_lt {E : Sig.{u}} (ω : ℕ → Call E) {j k : ℕ} (h : j < k) :
    CallPre (streamTake ω j) (ω j).1 (streamTake ω k) := by
  obtain ⟨r, hr⟩ := streamTake_split ω h
  exact ⟨(ω j).2, r, hr⟩

/-- Equal stream prefixes after a common list give equal elements. -/
theorem stream_eq_of_take {α : Type u} {ω : ℕ → α} {ω' : ℕ → α} {l : List α}
    (h : ∀ k, streamTake ω (l.length + k) = l ++ streamTake ω' k) (k : ℕ) :
    ω (l.length + k) = ω' k := by
  have h₁ := h (k + 1)
  rw [← Nat.add_assoc, streamTake_succ, streamTake_succ, h k, ← List.append_assoc] at h₁
  simpa using h₁

end Streams

/-! ## Infinite services -/

section Serve

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}

/-- The session rounds of an infinite service. -/
def serveRounds (ω : ℕ → Call (sig1 A B)) (l : ℕ → List (Call E)) :
    ℕ → A × List (Call E) × (B ⊕ PUnit.{u + 1}) :=
  fun k => ((ω k).1, l k, (ω k).2)

theorem served_serveRounds (ω : ℕ → Call (sig1 A B)) (l : ℕ → List (Call E)) (n : ℕ) :
    served (streamTake (serveRounds ω l) n) = streamTake ω n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [streamTake_succ, streamTake_succ, served_append, ih]; rfl

theorem servedLog_serveRounds (ω : ℕ → Call (sig1 A B)) (l : ℕ → List (Call E)) (n : ℕ) :
    servedLog (streamTake (serveRounds ω l) n) = logTake l n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [streamTake_succ, servedLog_append, ih, logTake, logTake, streamTake_succ]
    simp [serveRounds, servedLog]

theorem logTake_succ (l : ℕ → List (Call E)) (n : ℕ) :
    logTake l (n + 1) = logTake l n ++ l n := by
  simp [logTake, streamTake_succ]

theorem infServe_rounds {s : S} {ω : ℕ → Call (sig1 A B)} {l : ℕ → List (Call E)}
    {st : ℕ → S} (h : InfServe t s ω l st) (n : ℕ) :
    Rounds t s (streamTake (serveRounds ω l) n) (st n) := by
  induction n with
  | zero => rw [← h.zero]; exact .nil _
  | succ n ih => rw [streamTake_succ]; exact rounds_snoc ih (h.step n)

end Serve

/-! ## Call prefixes of the linked triple -/

section Link

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

theorem linkEnd_eq_ret {s : S} {e : End S' (B' ⊕ PUnit.{u + 1})} {x : B' ⊕ PUnit.{u + 1}}
    {σ : S × S'} (h : linkEnd s e = .ret x σ) : e = .ret x σ.2 ∧ s = σ.1 := by
  cases e with
  | ret y s' => simp only [linkEnd, End.ret.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | trap => cases h
  | div => cases h

theorem linkEnd_eq_trap {s : S} {e : End S' (B' ⊕ PUnit.{u + 1})}
    (h : linkEnd s e = .trap) : e = .trap := by
  cases e with
  | ret => cases h
  | trap => rfl
  | div => cases h

/-- A call inside served rounds is a pending call of the linked triple. -/
theorem pend_of_rounds {σ : S × S'} {a' : A'} {s₁ s₂ : S}
    {rs₀ rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    (h₀ : Rounds t σ.1 rs₀ s₁) (h : Rounds t s₁ rs s₂)
    (hauth : ∀ c m, CallPre c m (served (rs₀ ++ rs)) → (c, m) ∈ satP u σ.2 a')
    {c : List (Call E)} {m : E.Op} (hc : CallPre c m (servedLog rs)) :
    (servedLog rs₀ ++ c, m) ∈ (linkS t u).2.1 σ a' := by
  induction h generalizing rs₀ c with
  | nil => obtain ⟨_, _, h⟩ := hc; simp at h
  | @cons s s' _ a c₁ b rs hr _ ih =>
    rcases callPre_append (d₁ := c₁) (d₂ := servedLog rs) hc with hc₁ | ⟨c', rfl, hc'⟩
    · refine ⟨rs₀, s, a, c, h₀, hauth _ _ ?_, satP_of_beh hr hc₁, rfl⟩
      exact ⟨b, served rs, by simp⟩
    · have := ih (rs₀ := rs₀ ++ [(a, c₁, b)]) (rounds_snoc h₀ hr) (by simpa using hauth) hc'
      simpa using this

theorem auth_of_stream {s' : S'} {a' : A'} {ω : ℕ → Call (sig1 A B)} (hω : ω ∈ u.2.2 s' a')
    (n : ℕ) : ∀ c m, CallPre c m (streamTake ω n) → (c, m) ∈ satP u s' a' := by
  intro c m hc
  obtain ⟨j, rfl, rfl⟩ := callPre_streamTake hc
  exact .inr (.inr (.inr ⟨ω, hω, j, rfl, rfl⟩))

/-- **The call prefixes of the linked triple are its pending calls.** -/
theorem satP_linkS {σ : S × S'} {a' : A'} {x : List (Call E) × E.Op}
    (h : x ∈ satP (linkS t u) σ a') : x ∈ (linkS t u).2.1 σ a' := by
  obtain ⟨c, m⟩ := x
  -- calls inside the log of served rounds then a call prefix of the server
  have key : ∀ {rs s₁ a c₁}, Rounds t σ.1 rs s₁ → (served rs, a) ∈ satP u σ.2 a' →
      (∀ c' m', CallPre c' m' c₁ → (c', m') ∈ satP t s₁ a) →
      CallPre c m (servedLog rs ++ c₁) → (c, m) ∈ (linkS t u).2.1 σ a' := by
    intro rs s₁ a c₁ hR hu hc₁ hc
    rcases callPre_append hc with hc' | ⟨c', rfl, hc'⟩
    · simpa using pend_of_rounds (rs₀ := []) (.nil _) hR
        (fun _ _ h => satP_prefix hu (by simpa using h)) hc'
    · exact ⟨rs, s₁, a, c', hR, hu, hc₁ _ _ hc', rfl⟩
  -- calls inside the log of a finite part of an infinite service
  have keyω : ∀ {ω l st}, ω ∈ u.2.2 σ.2 a' → InfServe t σ.1 ω l st → ∀ n,
      CallPre c m (logTake l n) → (c, m) ∈ (linkS t u).2.1 σ a' := by
    intro ω l st hω hs n hc
    rw [← servedLog_serveRounds] at hc
    simpa using pend_of_rounds (rs₀ := []) (.nil _) (infServe_rounds hs n)
      (by simpa [served_serveRounds] using auth_of_stream hω n) hc
  rcases h with h | ⟨d, m', ⟨rs, s₁, a, c₁, hR, hu, hP, hd⟩, hc⟩ | ⟨d, e, hb, hc⟩ |
      ⟨ω, hω, k, rfl, rfl⟩
  · exact h
  · simp only at hd; subst hd
    exact key hR hu (fun _ _ h => satP_prefix hP h) hc
  · rcases hb with ⟨rs, s₁, e, hR, hb, he⟩ | ⟨rs, s₁, a, c₁, hR, hu, hd, he⟩ |
        ⟨ω, hω, l, st, n, hs, -, he⟩
    · obtain ⟨rfl, -⟩ := Prod.ext_iff.1 he
      simpa using pend_of_rounds (rs₀ := []) (.nil _) hR
        (fun _ _ h => satP_of_beh hb (by simpa using h)) hc
    · obtain ⟨rfl, -⟩ := Prod.ext_iff.1 he
      exact key hR hu (fun _ _ h => satP_of_beh hd h) hc
    · obtain ⟨rfl, -⟩ := Prod.ext_iff.1 he
      exact keyω hω hs n hc
  · rcases hω with ⟨rs, s₁, a, ω', hR, hu, hω', hk⟩ | ⟨ω', hω', l, st, hs, hun, hk⟩
    · rcases Nat.lt_or_ge k (servedLog rs).length with hlt | hge
      · have h0 := hk 0
        simp only [Nat.add_zero, streamTake_zero, List.append_nil] at h0
        have := key (c₁ := []) hR hu (fun _ _ h => by obtain ⟨_, _, h⟩ := h; simp at h)
          (by simpa [h0] using callPre_of_lt ω hlt)
        exact this
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
        refine ⟨rs, s₁, a, streamTake ω' j, hR, hu, ?_, hk j⟩
        rw [stream_eq_of_take hk j]
        exact .inr (.inr (.inr ⟨ω', hω', j, rfl, rfl⟩))
    · obtain ⟨n, hn⟩ := hun (k + 1)
      exact keyω hω' hs n (by rw [← hk n]; exact callPre_of_lt ω (by omega))

end Link

/-! ## Interactions -/

section Zip

variable {F G : Sig.{u}}

theorem zip_append {α β γ : Type u} {s₁ s₂ : List (α ⊕ β)} {t₁ t₂ : List (β ⊕ γ)}
    {p₁ p₂ : List (α ⊕ γ)} (h₁ : Zip s₁ t₁ p₁) (h₂ : Zip s₂ t₂ p₂) :
    Zip (s₁ ++ s₂) (t₁ ++ t₂) (p₁ ++ p₂) := by
  induction h₁ with
  | nil => exact h₂
  | left a _ ih => exact .left a ih
  | right c _ ih => exact .right c ih
  | sync b _ ih => exact .sync b ih

theorem zip_callMoves_left (c : List (Call E)) :
    Zip (callMoves c : List (Move E F)) ([] : List (Move F G)) (callMoves c : List (Move E G)) := by
  induction c with
  | nil => exact .nil
  | cons x c ih => exact .left _ (.left _ ih)

/-- The server's session rounds serve the client's calls, their logs visible. -/
theorem zip_served (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
    Zip (sroundsMoves rs : List (Move E (sig1 A B)))
      (callMoves (served rs) : List (Move (sig1 A B) G))
      (callMoves (servedLog rs) : List (Move E G)) := by
  induction rs with
  | nil => exact .nil
  | cons r rs ih =>
    obtain ⟨a, c, x⟩ := r
    have h := Zip.sync (.ask a) (zip_append (zip_callMoves_left (F := sig1 A B) (G := G) c)
      (Zip.sync (.ans a x) ih))
    simpa [sroundMoves] using h

end Zip

/-! ## The forward direction -/

section Fwd

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

/-- Related states of the server, the client and the linked session automata. -/
inductive J (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})) :
    TSt E S A → TSt (sig1 A B) S' A' → TSt E (S × S') A' → Prop
  | idle (s : S) (s' : S') : J t u (.idle s) (.idle s') (.idle (s, s'))
  | run (σ : S × S') (a' : A') (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (s : S) :
      Rounds t σ.1 rs s → J t u (.idle s) (.run σ.2 a' (served rs)) (.run σ a' (servedLog rs))
  | call (σ : S × S') (a' : A') (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (s : S)
      (a : A) (c : List (Call E)) : Rounds t σ.1 rs s → (served rs, a) ∈ satP u σ.2 a' →
      J t u (.run s a c) (.wait σ.2 a' (served rs) a) (.run σ a' (servedLog rs ++ c))
  | wait (σ : S × S') (a' : A') (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) (s : S)
      (a : A) (c : List (Call E)) (m : E.Op) : Rounds t σ.1 rs s →
      (served rs, a) ∈ satP u σ.2 a' →
      J t u (.wait s a c m) (.wait σ.2 a' (served rs) a) (.wait σ a' (servedLog rs ++ c) m)
  | dead (s : S) : J t u (.idle s) .dead .dead
  | stuck (s : S) (a' : A') : J t u (.idle s) (.stuck a') (.stuck a')

/-- **Forward**: the visible part of an interaction is a run of the linked session automaton. -/
theorem fwd (hnt : NoPlainTrap t) {sv : List (Move E (sig1 A B))}
    {cv : List (Move (sig1 A B) (sig1 A' B'))} {p : List (Move E (sig1 A' B'))}
    (hz : Zip sv cv p) :
    ∀ {x x' y y' z}, J t u x y z → SRun t x sv x' → SRun u y cv y' →
      ∃ z', SRun (linkS t u) z p z' ∧ J t u x' y' z' := by
  induction hz with
  | nil =>
    intro x x' y y' z hJ hv hc
    cases hv; cases hc
    exact ⟨z, .nil _, hJ⟩
  | left e _ ih =>
    intro x x' y y' z hJ hv hc
    cases hv with
    | cons hst hr =>
      cases hst with
      | call s a c m hP =>
        cases hJ with
        | call σ a' rs _ _ _ hR hu =>
          obtain ⟨z', hz', hJ'⟩ := ih (J.wait σ _ rs s a c m hR hu) hr hc
          exact ⟨z', .cons (.call σ _ _ m (.inl ⟨rs, s, a, c, hR, hu, hP, rfl⟩)) hz', hJ'⟩
      | reply s a c m n =>
        cases hJ with
        | wait σ a' rs _ _ _ _ hR hu =>
          obtain ⟨z', hz', hJ'⟩ := ih (J.call σ _ rs s a (c ++ [⟨m, n⟩]) hR hu) hr hc
          have hs := SStep.reply (t := linkS t u) σ a' (servedLog rs ++ c) m n
          rw [List.append_assoc] at hs
          exact ⟨z', .cons hs hz', hJ'⟩
  | right g _ ih =>
    intro x x' y y' z hJ hv hc
    cases hc with
    | cons hst hr =>
      cases hst with
      | ask s' a' =>
        cases hJ with
        | idle s _ =>
          obtain ⟨z', hz', hJ'⟩ := ih (J.run (u := u) (s, s') a' [] s (.nil _)) hv hr
          exact ⟨z', .cons (.ask (s, s') a') hz', hJ'⟩
      | ret _ _ _ b s'' hb =>
        cases hJ with
        | run σ a' rs s hR =>
          obtain ⟨z', hz', hJ'⟩ := ih (J.idle (u := u) s s'') hv hr
          exact ⟨z', .cons (.ret σ _ _ b (s, s'') (.inl ⟨rs, s, .ret b s'', hR, hb, rfl⟩)) hz',
            hJ'⟩
      | trap _ _ _ hb =>
        cases hJ with
        | run σ a' rs s hR =>
          obtain ⟨z', hz', hJ'⟩ := ih (J.dead (u := u) s) hv hr
          exact ⟨z', .cons (.trap σ _ _ (.inl ⟨rs, s, .trap, hR, hb, rfl⟩)) hz', hJ'⟩
      | deadAsk a' =>
        cases hJ with
        | dead s =>
          obtain ⟨z', hz', hJ'⟩ := ih (J.stuck (u := u) s a') hv hr
          exact ⟨z', .cons (.deadAsk a') hz', hJ'⟩
  | sync b _ ih =>
    intro x x' y y' z hJ hv hc
    cases hv with
    | cons hst hr =>
      cases hc with
      | cons hct hcr =>
        cases hst with
        | ask s a =>
          cases hct with
          | call _ _ _ _ hP =>
            cases hJ with
            | run σ a' rs _ hR =>
              have hJ' := J.call σ _ rs s a [] hR hP
              rw [List.append_nil] at hJ'
              exact ih hJ' hr hcr
        | ret s a c x s₂ hb =>
          cases hct with
          | reply _ a' =>
            cases hJ with
            | call σ _ rs _ _ _ hR hu =>
              have hJ' := J.run (u := u) σ a' (rs ++ [(a, c, x)]) s₂ (rounds_snoc hR hb)
              simp only [served_append, served_cons, served_nil, servedLog_append,
                servedLog_cons, servedLog_nil, List.append_nil] at hJ'
              exact ih hJ' hr hcr
        | trap s a c hb => exact absurd hb (hnt s a c)
        | deadAsk => cases hJ

end Fwd

/-! ## The backward direction -/

section Bwd

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

/-- The client asks `a'` and makes the served calls, served by the server's rounds. -/
theorem core_served {σ : S × S'} {a' : A'} {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    {s₁ : S} (hR : Rounds t σ.1 rs s₁)
    (hauth : ∀ c m, CallPre c m (served rs) → (c, m) ∈ satP u σ.2 a') :
    Zip (sroundsMoves rs) (.inr (.ask a') :: callMoves (served rs))
        (.inr (.ask a') :: callMoves (servedLog rs) : List (Move E (sig1 A' B'))) ∧
      SRun t (.idle σ.1) (sroundsMoves rs) (.idle s₁) ∧
      SRun u (.idle σ.2) (.inr (.ask a') :: callMoves (served rs)) (.run σ.2 a' (served rs)) := by
  refine ⟨.right _ (zip_served rs), run_rounds hR, .cons (.ask _ _) ?_⟩
  simpa using run_callMoves (t := u) (s := σ.2) (a := a') (served rs) (c₀ := [])
    (by simpa using hauth)

/-- The client waits on the served call `a`, the server runs it after the calls `c₁`. -/
theorem core_run {σ : S × S'} {a' : A'} {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    {s₁ : S} {a : A} {c₁ : List (Call E)} (hR : Rounds t σ.1 rs s₁)
    (hu : (served rs, a) ∈ satP u σ.2 a')
    (hc₁ : ∀ c m, CallPre c m c₁ → (c, m) ∈ satP t s₁ a) :
    Zip (sroundsMoves rs ++ .inr (.ask a) :: callMoves c₁)
        (.inr (.ask a') :: (callMoves (served rs) ++ [.inl (.ask a)]))
        (.inr (.ask a') :: callMoves (servedLog rs ++ c₁) : List (Move E (sig1 A' B'))) ∧
      SRun t (.idle σ.1) (sroundsMoves rs ++ .inr (.ask a) :: callMoves c₁) (.run s₁ a c₁) ∧
      SRun u (.idle σ.2) (.inr (.ask a') :: (callMoves (served rs) ++ [.inl (.ask a)]))
        (.wait σ.2 a' (served rs) a) := by
  obtain ⟨hz, hv, hc⟩ := core_served (a' := a') hR (fun _ _ h => satP_prefix hu h)
  refine ⟨?_, hv.append (.cons (.ask _ _) ?_), ?_⟩
  · have := zip_append hz (Zip.sync (.ask a) (zip_callMoves_left (F := sig1 A B)
      (G := sig1 A' B') c₁))
    simpa using this
  · simpa using run_callMoves (t := t) (s := s₁) (a := a) c₁ (c₀ := []) (by simpa using hc₁)
  · have := hc.append (.single (.call σ.2 a' (served rs) a hu))
    simpa using this

/-- One completed linked round is the visible part of an interaction. -/
theorem bwd_round {σ σ' : S × S'} {a' : A'} {c : List (Call E)} {x : B' ⊕ PUnit.{u + 1}}
    (h : (c, .ret x σ') ∈ (linkS t u).1 σ a') :
    ∃ sv cv, Zip sv cv (sroundMoves (a', c, x)) ∧ SRun t (.idle σ.1) sv (.idle σ'.1) ∧
      SRun u (.idle σ.2) cv (.idle σ'.2) := by
  rcases h with ⟨rs, s₁, e, hR, hb, he⟩ | ⟨_, _, _, _, _, _, _, he⟩ | ⟨_, _, _, _, _, _, _, he⟩
  · obtain ⟨rfl, he⟩ := Prod.ext_iff.1 he
    obtain ⟨rfl, rfl⟩ := linkEnd_eq_ret he.symm
    obtain ⟨hz, hv, hc⟩ := core_served (a' := a') hR (fun _ _ h => satP_of_beh hb h)
    refine ⟨_, _, ?_, hv, hc.append (.single (.ret _ _ _ _ _ hb))⟩
    have := zip_append hz (Zip.right (.ans a' x) .nil)
    simpa [sroundMoves] using this
  · cases (Prod.ext_iff.1 he).2
  · cases (Prod.ext_iff.1 he).2

/-- Completed linked rounds are the visible part of an interaction. -/
theorem bwd_rounds {σ₀ σ₁ : S × S'} {rs : List (A' × List (Call E) × (B' ⊕ PUnit.{u + 1}))}
    (h : Rounds (linkS t u) σ₀ rs σ₁) :
    ∃ sv cv, Zip sv cv (sroundsMoves rs) ∧ SRun t (.idle σ₀.1) sv (.idle σ₁.1) ∧
      SRun u (.idle σ₀.2) cv (.idle σ₁.2) := by
  induction h with
  | nil => exact ⟨[], [], .nil, .nil _, .nil _⟩
  | cons hr _ ih =>
    obtain ⟨sv, cv, hz, hv, hc⟩ := bwd_round hr
    obtain ⟨sv', cv', hz', hv', hc'⟩ := ih
    exact ⟨_, _, zip_append hz hz', hv.append hv', hc.append hc'⟩

/-- A play of the composite, given by its interaction. -/
def Realized (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})) (σ : S × S')
    (p : List (Move E (sig1 A' B'))) : Prop :=
  ∃ sv cv, Zip sv cv p ∧ (∃ x, SRun t (.idle σ.1) sv x) ∧ ∃ y, SRun u (.idle σ.2) cv y

theorem Realized.rounds_append {σ₀ σ₁ : S × S'}
    {rs : List (A' × List (Call E) × (B' ⊕ PUnit.{u + 1}))} {p : List (Move E (sig1 A' B'))}
    (h : Rounds (linkS t u) σ₀ rs σ₁) (hp : Realized t u σ₁ p) :
    Realized t u σ₀ (sroundsMoves rs ++ p) := by
  obtain ⟨sv, cv, hz, hv, hc⟩ := bwd_rounds h
  obtain ⟨sv', cv', hz', ⟨x, hx⟩, y, hy⟩ := hp
  exact ⟨_, _, zip_append hz hz', ⟨x, hv.append hx⟩, y, hc.append hy⟩

/-- A pending call of the linked triple is the visible part of an interaction. -/
theorem bwd_wait {σ : S × S'} {a' : A'} {c : List (Call E)} {m : E.Op}
    (h : (c, m) ∈ (linkS t u).2.1 σ a') :
    ∃ sv cv s₁ a c₁, Zip sv cv (.inr (.ask a') :: (callMoves c ++ [.inl (.ask m)])) ∧
      SRun t (.idle σ.1) sv (.wait s₁ a c₁ m) ∧ ∃ y, SRun u (.idle σ.2) cv y := by
  obtain ⟨rs, s₁, a, c₁, hR, hu, hP, rfl⟩ := h
  obtain ⟨hz, hv, hc⟩ := core_run hR hu (fun _ _ h => satP_prefix hP h)
  refine ⟨_, _, s₁, a, c₁, ?_, hv.append (.single (.call s₁ a c₁ m hP)), _, hc⟩
  have := hz.append_left (.ask m)
  simpa using this

/-- The partial round of a run of the linked session automaton is realized. -/
theorem bwd_tail {σ : S × S'} {q : List (Move E (sig1 A' B'))} {z : TSt E (S × S') A'}
    (h : Shape (linkS t u) σ q z) : Realized t u σ q := by
  cases z with
  | idle σ₁ =>
    obtain ⟨rs, hrs, rfl⟩ := h
    obtain ⟨sv, cv, hz, hv, hc⟩ := bwd_rounds hrs
    exact ⟨sv, cv, hz, ⟨_, hv⟩, _, hc⟩
  | run σ₁ a' c =>
    obtain ⟨rs, hrs, rfl, hc⟩ := h
    refine Realized.rounds_append hrs ?_
    rcases hc with rfl | ⟨c₀, m, n, rfl, hP⟩
    · exact ⟨[], _, .right _ .nil, ⟨_, .nil _⟩, _, .single (.ask _ a')⟩
    · obtain ⟨sv, cv, s₁, a, c₁, hz, hv, y, hy⟩ := bwd_wait (satP_linkS hP)
      refine ⟨_, cv, ?_, ⟨_, hv.append (.single (.reply s₁ a c₁ m n))⟩, y, hy⟩
      have := hz.append_left (.ans m n)
      simpa using this
  | wait σ₁ a' c m =>
    obtain ⟨rs, hrs, rfl, hP⟩ := h
    refine Realized.rounds_append hrs ?_
    obtain ⟨sv, cv, s₁, a, c₁, hz, hv, y, hy⟩ := bwd_wait (satP_linkS hP)
    exact ⟨sv, cv, hz, ⟨_, hv⟩, y, hy⟩
  | dead =>
    obtain ⟨rs, σ₁, a', c, hrs, hb, rfl⟩ := h
    refine Realized.rounds_append hrs ?_
    rcases hb with ⟨rs', s₁, e, hR, hb, he⟩ | ⟨_, _, _, _, _, _, _, he⟩ |
        ⟨_, _, _, _, _, _, _, he⟩
    · obtain ⟨rfl, he⟩ := Prod.ext_iff.1 he
      cases linkEnd_eq_trap he.symm
      obtain ⟨hz, hv, hc⟩ := core_served (a' := a') hR (fun _ _ h => satP_of_beh hb h)
      refine ⟨_, _, ?_, ⟨_, hv⟩, _, hc.append (.single (.trap _ _ _ hb))⟩
      have := zip_append hz (Zip.right (.ans a' (.inr PUnit.unit)) .nil)
      simpa [sroundMoves] using this
    · cases (Prod.ext_iff.1 he).2
    · cases (Prod.ext_iff.1 he).2
  | stuck a'' =>
    obtain ⟨rs, σ₁, a', c, hrs, hb, rfl⟩ := h
    rw [List.append_assoc]
    refine Realized.rounds_append hrs ?_
    rcases hb with ⟨rs', s₁, e, hR, hb, he⟩ | ⟨_, _, _, _, _, _, _, he⟩ |
        ⟨_, _, _, _, _, _, _, he⟩
    · obtain ⟨rfl, he⟩ := Prod.ext_iff.1 he
      cases linkEnd_eq_trap he.symm
      obtain ⟨hz, hv, hc⟩ := core_served (a' := a') hR (fun _ _ h => satP_of_beh hb h)
      refine ⟨_, _, ?_, ⟨_, hv⟩, _,
        (hc.append (.single (.trap _ _ _ hb))).append (.single (.deadAsk a''))⟩
      have := zip_append (zip_append hz (Zip.right (.ans a' (.inr PUnit.unit)) .nil))
        (Zip.right (.ask a'') .nil)
      simpa [sroundMoves] using this
    · cases (Prod.ext_iff.1 he).2
    · cases (Prod.ext_iff.1 he).2

/-- **Backward**: a run of the linked session automaton is the visible part of an
interaction. -/
theorem bwd_play {σ : S × S'} {p : List (Move E (sig1 A' B'))} {z : TSt E (S × S') A'}
    (h : SRun (linkS t u) (.idle σ) p z) : Realized t u σ p :=
  bwd_tail (shape h)

end Bwd

/-! ## Finite plays -/

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

/-- **The finite plays of the composite are those of the linked session.** -/
theorem mem_comp_iff (hnt : NoPlainTrap t) {s₀ : S} {s₀' : S'} {p : List (Move E (sig1 A' B'))} :
    p ∈ ((threadS t s₀).comp (threadS u s₀')).toStrategy ↔
      p ∈ (threadS (linkS t u) (s₀, s₀')).toStrategy := by
  constructor
  · rintro ⟨sv, hsv, cv, hcv, hz⟩
    obtain ⟨x, hx⟩ := mem_plays.1 hsv
    obtain ⟨y, hy⟩ := mem_plays.1 hcv
    obtain ⟨z, hz', -⟩ := fwd hnt hz (J.idle s₀ s₀') hx hy
    exact mem_plays.2 ⟨z, hz'⟩
  · intro hp
    obtain ⟨z, hz⟩ := mem_plays.1 hp
    obtain ⟨sv, cv, hzip, ⟨x, hx⟩, y, hy⟩ := bwd_play hz
    exact ⟨sv, mem_plays.2 ⟨x, hx⟩, cv, mem_plays.2 ⟨y, hy⟩, hzip⟩

end Silmaril.Proofs.Games.Abstract.SessionLink
