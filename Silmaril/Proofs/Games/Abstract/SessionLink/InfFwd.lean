module

public import Silmaril.Proofs.Games.Abstract.SessionLink.Stage
public import Silmaril.Proofs.Games.Abstract.SessionLink.InfBwd
import Mathlib.Data.List.Basic

/-!
# Linking sessions: chatter and infinite plays, forward direction (proofs)

For a server without plain traps and store-deterministic:

* `chatter_fwd`: hidden chatter of the composite is a linked divergence: the client streams inside
  one round, its calls served by a coherent infinite play of the server with finitely many server
  calls (the linked chatter `div`);
* `inf_fwd`: an infinite play of the composite is one of the linked session: the client completes
  infinitely many rounds (each a linked round), or streams inside one round with infinitely many
  server calls (a linked stream), or waits on one call while the server streams inside it (a linked
  stream).

The client is classified by its limit (`StratSession.mem_inf_iff`), the server by its limit with
coherent stores (`StratSession.mem_inf_iff_of_storeDet`); mismatched cases are excluded by counting
the hidden events of both sides (`upper_eq_lower`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLink

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionLink

universe u

variable {E : Sig.{u}} {S S' A B A' B' : Type u}

/-! ## Helpers -/

theorem SStep.pos {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {x y : TSt E S A}
    {o : Move E (sig1 A B)} (h : SStep t x o y) : Step (x.pos (B := B)) o (y.pos (B := B)) := by
  cases h <;> constructor

theorem SRun.pos {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {x y : TSt E S A}
    {q : List (Move E (sig1 A B))} (h : SRun t x q y) : Path (x.pos (B := B)) q (y.pos (B := B)) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons h.pos ih

theorem length_upper_le_length {F G : Sig.{u}} (s : List (Move F G)) :
    (upper s).length ≤ s.length := by
  have := length_lower_add_upper s; omega

/-- A chain bounded by an increasing sequence of lists, and unbounded, has their limit. -/
theorem lim_eq_of_bounds {α : Type u} {c : Chain α} (hu : c.Unbounded) {L : ℕ → List α}
    (hL : ∀ K, L K <+: L (K + 1)) (h : ∀ n, ∃ K, c n <+: L K) :
    c.lim = {q | ∃ K, q <+: L K} := by
  have hLm : ∀ {K K'}, K ≤ K' → L K <+: L K' := fun hK => by
    induction hK with
    | refl => exact List.prefix_refl _
    | step _ ih => exact ih.trans (hL _)
  ext q
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨K, hK⟩ := h n
    exact ⟨K, hn.trans hK⟩
  · rintro ⟨K, hK⟩
    obtain ⟨n, hn⟩ := hu q.length
    obtain ⟨K', hK'⟩ := h n
    refine ⟨n, List.prefix_of_prefix_length_le (hK.trans (hLm (le_max_left K K')))
      (hK'.trans (hLm (le_max_right K K'))) hn⟩

/-- A prefix inside a partial round has one more upper event than the completed rounds. -/
theorem length_upper_inround {F G : Sig.{u}} {P q : List (Move F G)} {g : Ev G}
    {D : List (Call F)} (hq : q <+: P ++ .inr g :: callMoves D) (hl : P.length < q.length) :
    (upper q).length = (upper P).length + 1 := by
  obtain ⟨X, rfl, hX⟩ := prefix_append_long hq hl.le
  rcases X with _ | ⟨o, Q⟩
  · simp at hl
  obtain ⟨rfl, hQ⟩ := List.cons_prefix_cons.1 hX
  have := length_upper_le hQ
  simp only [upper_callMoves, List.length_nil, Nat.le_zero, List.length_eq_zero_iff] at this
  simp [upper_append, this]

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

/-- **Assembling a linked stream**: if from some stage on, every visible play is the same
completed linked rounds to `σ`, the question `a'`, and a prefix of the calls of `ω`, the visible
limit is the linked stream play. -/
theorem lim_linked_stream {s₀ : S} {s₀' : S'}
    (i : DStrategy.InfInteraction (threadS t s₀) (threadS u s₀')) (hu : i.p.Unbounded)
    {σ : S × S'} {a' : A'} {ω : ℕ → Call E} (hω : ω ∈ (linkS t u).2.2 σ a') {n₁ U : ℕ}
    (hU : ∀ n, n₁ ≤ n → (upper (i.p n)).length = U)
    (hst : ∀ n, n₁ ≤ n → ∃ rsL Q K, Rounds (linkS t u) (s₀, s₀') rsL σ ∧
      i.p n = sroundsMoves rsL ++ .inr (.ask a') :: Q ∧ Q <+: callMoves (streamTake ω K) ∧
      (upper Q) = []) :
    i.p.lim ∈ (threadS (linkS t u) (s₀, s₀')).inf := by
  obtain ⟨rsL, Q₁, K₁, hrsL, hp₁, -, hQ₁⟩ := hst n₁ le_rfl
  have hpre : ∀ n, n₁ ≤ n → ∃ K, i.p n <+: sroundsMoves rsL ++ .inr (.ask a') ::
      callMoves (streamTake ω K) := by
    intro n hn
    obtain ⟨rsL', Q, K, -, hp, hQ, hQu⟩ := hst n hn
    have h₁ : sroundsMoves rsL ++ [.inr (.ask a')] <+: i.p n :=
      ((hp₁ ▸ ⟨Q₁, by simp⟩ : sroundsMoves rsL ++ [.inr (.ask a')] <+: i.p n₁)).trans
        (i.mono_p.le hn)
    have h₂ : sroundsMoves rsL' ++ [.inr (.ask a')] <+: i.p n := hp ▸ ⟨Q, by simp⟩
    have hl : (upper (sroundsMoves rsL : List (Move E (sig1 A' B')))).length =
        (upper (sroundsMoves rsL' : List (Move E (sig1 A' B')))).length := by
      have e₁ := hU n₁ le_rfl
      have e₂ := hU n hn
      rw [hp₁] at e₁; rw [hp] at e₂
      simp [upper_append, hQ₁, hQu] at e₁ e₂
      omega
    obtain ⟨heq, -⟩ := eq_of_upper h₁ h₂ hl
    refine ⟨K, ?_⟩
    rw [hp, ← heq]
    exact (List.prefix_append_right_inj _).2 (List.cons_prefix_cons.2 ⟨rfl, hQ⟩)
  have hlim : i.p.lim = streamPlay (sroundsMoves rsL) a' ω := by
    refine lim_eq_of_bounds hu (fun K => (List.prefix_append_right_inj _).2
      (List.cons_prefix_cons.2 ⟨rfl, callMoves_prefix (streamTake_prefix ω (by omega))⟩))
      fun n => ?_
    rcases le_total n₁ n with h | h
    · exact hpre n h
    · obtain ⟨K, hK⟩ := hpre n₁ le_rfl
      exact ⟨K, (i.mono_p.le h).trans hK⟩
  rw [hlim]
  exact mem_inf_of_stream (run_rounds hrsL) hω

/-! ## Counting hidden events -/

/-- A chain whose limit completes infinitely many rounds has unboundedly many upper events. -/
theorem upper_unbounded_of_rounds {F₁ : Sig.{u}} {A₁ B₁ : Type u}
    {c : Chain (Move F₁ (sig1 A₁ B₁))} (hm : c.Mono) (hu : c.Unbounded) {a : ℕ → A₁}
    {r : ℕ → List (Call F₁) × (B₁ ⊕ PUnit.{u + 1})} (hlim : c.lim = sroundsPlay a r) (k : ℕ) :
    ∃ n, 2 * k ≤ (upper (c n)).length := by
  have hI := Chain.isInfPlay_lim hm hu
  have hk : sroundsMoves (streamTake (fun i => (a i, r i)) k) ∈ c.lim :=
    hlim ▸ Chain.mem_lim_self _ k
  obtain ⟨n, hn⟩ := hu (sroundsMoves (streamTake (fun i => (a i, r i)) k)).length
  have hp := hI.prefix_of_length_le hk (Chain.mem_lim_self c n) hn
  refine ⟨n, ?_⟩
  have := length_upper_le hp
  rwa [length_upper_sroundsMoves, length_streamTake] at this

/-- The client streaming inside a round makes unboundedly many hidden calls. -/
theorem lower_unbounded_of_stream {F₁ : Sig.{u}} {A₁ B₁ : Type u}
    {c : Chain (Move F₁ (sig1 A₁ B₁))} (hu : c.Unbounded)
    {pre : List (Move F₁ (sig1 A₁ B₁))} {a : A₁} {ω : ℕ → Call F₁}
    (hlim : c.lim = streamPlay pre a ω) (k : ℕ) : ∃ n, k ≤ (lower (c n)).length := by
  obtain ⟨n, hn⟩ := hu (k + (upper pre).length + 1)
  refine ⟨n, ?_⟩
  obtain ⟨K, hK⟩ : c n ∈ streamPlay pre a ω := hlim ▸ Chain.mem_lim_self c n
  have h₁ := length_upper_le hK
  have h₂ := length_lower_add_upper (c n)
  simp [upper_append] at h₁
  omega

/-- **The server plays a coherent infinite play** when the client streams inside a round. -/
theorem server_coherent (htd : StoreDet t) {s₀ : S} {s₀' : S'}
    (i : DStrategy.InfInteraction (threadS t s₀) (threadS u s₀')) (htu : i.t.Unbounded)
    {pre : List (Move (sig1 A B) (sig1 A' B'))} {a' : A'} {ω : ℕ → Call (sig1 A B)}
    (hlimt : i.t.lim = streamPlay pre a' ω) :
    ∃ as r st, InfRounds t s₀ as r st ∧ i.s.lim = sroundsPlay as r := by
  have hlow := lower_unbounded_of_stream htu hlimt
  have hsu : i.s.Unbounded := fun k => by
    obtain ⟨n, hn⟩ := hlow k
    have := congrArg List.length (upper_eq_lower (i.zip n))
    have := length_upper_le_length (i.s n)
    exact ⟨n, by omega⟩
  rcases (StratSession.mem_inf_iff_of_storeDet htd).1 (i.lim_s hsu) with
    ⟨R_s, s₁, a_s, ω_t, -, -, hlims⟩ | h
  · exfalso
    obtain ⟨n, hn⟩ := hlow (2 * R_s.length + 2)
    obtain ⟨K, hK⟩ : i.s n ∈ streamPlay (sroundsMoves R_s) a_s ω_t :=
      hlims ▸ Chain.mem_lim_self _ n
    have h₁ := length_upper_le hK
    have h₂ := congrArg List.length (upper_eq_lower (i.zip n))
    simp [upper_append, length_upper_sroundsMoves] at h₁
    omega
  · exact h

/-! ## Chatter -/

/-- **Hidden chatter of the composite is a linked divergence.** -/
theorem chatter_fwd (hnt : NoPlainTrap t) (htd : StoreDet t) {s₀ : S} {s₀' : S'}
    (i : DStrategy.InfInteraction (threadS t s₀) (threadS u s₀')) {p : List (Move E (sig1 A' B'))}
    (hi : ∀ n, i.p n = p) : p ∈ (threadS (linkS t u) (s₀, s₀')).div := by
  obtain ⟨-, htu, -, hlt⟩ := i.chatter_inf hi
  rcases StratSession.mem_inf_iff.1 hlt with ⟨rs_c, s', a', ω, hrc, hω, hlimt⟩ |
      ⟨ac, rc, hlimt, -⟩
  swap
  · exfalso
    obtain ⟨n, hn⟩ := upper_unbounded_of_rounds i.mono_t htu hlimt (p.length + 1)
    have h₁ := upper_vis (i.zip n)
    rw [hi n] at h₁
    have := length_upper_le_length p
    rw [h₁] at this
    omega
  obtain ⟨as, r, st, hinf, hlims⟩ := server_coherent htd i htu hlimt
  set N := (rs_c.flatMap fun r => r.2.1).length with hNdef
  have hN : (lower (sroundsMoves rs_c : List (Move (sig1 A B) (sig1 A' B')))).length = 2 * N :=
    length_lower_sroundsMoves rs_c
  set l : ℕ → List (Call E) := fun k => (r (N + k)).1 with hldef
  set C₀ := (sroundsMoves rs_c : List (Move (sig1 A B) (sig1 A' B'))).length
  obtain ⟨n₁, hn₁⟩ := htu (C₀ + 1)
  have hst : ∀ n, n₁ ≤ n → ∃ j c z, SRun (linkS t u) (.idle (s₀, s₀')) (i.p n) z ∧
      (∀ k < j, (⟨as (N + k), (r (N + k)).2⟩ : Call (sig1 A B)) = ω k) ∧
      (i.t n).length ≤ C₀ + 2 * j + 2 ∧
      ((z = .run (st N, s') a' (logTake l j ++ c) ∧ c <+: l j) ∨
        ∃ m, z = .wait (st N, s') a' (logTake l j ++ c) m ∧ CallPre c m (l j)) :=
    fun n hn => stage_clientStream hnt htd i hrc hω hlimt hinf hlims hN
      (by have := (i.mono_t.le hn).length_le; omega)
  have hjun : ∀ k, ∃ n, n₁ ≤ n ∧ ∃ j c z, k ≤ j ∧ SRun (linkS t u) (.idle (s₀, s₀')) (i.p n) z ∧
      (∀ k < j, (⟨as (N + k), (r (N + k)).2⟩ : Call (sig1 A B)) = ω k) ∧
      ((z = .run (st N, s') a' (logTake l j ++ c) ∧ c <+: l j) ∨
        ∃ m, z = .wait (st N, s') a' (logTake l j ++ c) m ∧ CallPre c m (l j)) := by
    intro k
    obtain ⟨n, hn, hl⟩ := i.mono_t.unbounded_ge htu (C₀ + 2 * k + 3) n₁
    obtain ⟨j, c, z, hz, hag, hlen, hform⟩ := hst n hn
    exact ⟨n, hn, j, c, z, by omega, hz, hag, hform⟩
  -- the position of a chattering composite is running
  obtain ⟨g, hg⟩ := DStrategy.compDiv_run (σ := threadS t s₀) (τ := threadS u s₀') (.inr ⟨i, hi⟩)
  have hrun : ∀ {z : TSt E (S × S') A'}, SRun (linkS t u) (.idle (s₀, s₀')) p z →
      ∀ σ a c m, z ≠ .wait σ a c m := by
    rintro z hz σ a c m rfl
    cases hg.det hz.pos
  -- the logs are bounded, hence eventually empty
  have hbd : ∀ k, (logTake l k).length ≤ p.length := by
    intro k
    obtain ⟨n, -, j, c, z, hkj, hz, -, hform⟩ := hjun k
    rw [hi n] at hz
    rcases hform with ⟨rfl, -⟩ | ⟨m, rfl, -⟩
    · obtain ⟨rs, -, hp, -⟩ := shape hz
      have h₁ : logTake l k <+: logTake l j := by
        obtain ⟨r', hr'⟩ := streamTake_prefix l hkj
        exact ⟨r'.flatten, by simp only [logTake]; rw [← hr', List.flatten_append]⟩
      have := congrArg List.length hp
      simp [length_callMoves] at this
      have := h₁.length_le
      omega
    · exact absurd rfl (hrun hz _ _ _ m)
  have hmono : Chain.Mono (logTake l) := fun k => by
    rw [logTake_succ]; exact List.prefix_append _ _
  obtain ⟨n₀, hn₀⟩ := hmono.eventually_const fun h => by
    obtain ⟨k, hk⟩ := h (p.length + 1)
    have := hbd k; omega
  have hl : ∀ k, n₀ ≤ k → l k = [] := fun k hk => by
    have h₁ := hn₀ (k + 1) (by omega)
    rw [logTake_succ, hn₀ k hk] at h₁
    simpa using h₁
  -- the coherent service of the client's stream
  have hag : ∀ k, (⟨as (N + k), (r (N + k)).2⟩ : Call (sig1 A B)) = ω k := fun k => by
    obtain ⟨n, -, j, c, z, hkj, -, hag, -⟩ := hjun (k + 1)
    exact hag k (by omega)
  have hserve : InfServe t (st N, s').1 ω l (fun k => st (N + k)) :=
    ⟨rfl, fun k => by
      have h := hinf.step (N + k)
      rw [← hag k]
      exact h⟩
  obtain ⟨n, -, j, c, z, hkj, hz, -, hform⟩ := hjun n₀
  rw [hi n] at hz
  rcases hform with ⟨rfl, hc⟩ | ⟨m, rfl, -⟩
  · rw [hl j hkj, List.prefix_nil] at hc
    subst hc
    rw [List.append_nil, hn₀ j hkj] at hz
    exact mem_div.2 ⟨_, a', _, hz, .inr (.inr ⟨ω, hω, l, _, n₀, hserve, hl, rfl⟩)⟩
  · exact absurd rfl (hrun hz _ _ _ m)

/-! ## Infinite plays -/

/-- A linked round shape inside the current round, as a prefix of the calls of a stream. -/
theorem shape_inround {s₀ : S} {s₀' : S'} {σ : S × S'} {a' : A'}
    {p : List (Move E (sig1 A' B'))} {C : List (Call E)} {T : List (Move E (sig1 A' B'))}
    {z : TSt E (S × S') A'} (hz : SRun (linkS t u) (.idle (s₀, s₀')) p z)
    (hT : (T = [] ∧ z = .run σ a' C) ∨ ∃ m, T = [.inl (.ask m)] ∧ z = .wait σ a' C m) :
    ∃ rsL, Rounds (linkS t u) (s₀, s₀') rsL σ ∧
      p = sroundsMoves rsL ++ .inr (.ask a') :: (callMoves C ++ T) := by
  rcases hT with ⟨rfl, rfl⟩ | ⟨m, rfl, rfl⟩
  · obtain ⟨rsL, hrsL, hp, -⟩ := shape hz
    exact ⟨rsL, hrsL, by simpa using hp⟩
  · obtain ⟨rsL, hrsL, hp, -⟩ := shape hz
    exact ⟨rsL, hrsL, hp⟩

/-- **The client completes infinitely many rounds**: the visible limit completes infinitely many
linked rounds. -/
theorem inf_fwd_rounds (hnt : NoPlainTrap t) {s₀ : S} {s₀' : S'}
    (i : DStrategy.InfInteraction (threadS t s₀) (threadS u s₀')) (hu : i.p.Unbounded)
    {ac : ℕ → A'} {rc : ℕ → List (Call (sig1 A B)) × (B' ⊕ PUnit.{u + 1})}
    (hlimt : i.t.lim = sroundsPlay ac rc)
    (hR : ∀ k, ∃ s, Rounds u s₀' (streamTake (fun i => (ac i, rc i)) k) s) :
    i.p.lim ∈ (threadS (linkS t u) (s₀, s₀')).inf := by
  have hI := Chain.isInfPlay_lim i.mono_p hu
  refine mem_inf_of_rounds hI fun x hx => ?_
  obtain ⟨s, hRk⟩ := hR (x.length + 1)
  obtain ⟨m, hm⟩ : sroundsMoves (streamTake (fun i => (ac i, rc i)) (x.length + 1)) ∈ i.t.lim :=
    hlimt ▸ Chain.mem_lim_self _ _
  obtain ⟨s', p', hs', hp', hz⟩ := zip_prefix_right (i.zip m) hm
  obtain ⟨xs, hxs⟩ := mem_plays.1 (i.mem_s m)
  obtain ⟨Z, hZ⟩ := hs'
  rw [← hZ] at hxs
  obtain ⟨xs', hxs', -⟩ := hxs.of_append
  obtain ⟨z', hz', hJ⟩ := fwd hnt hz (J.idle s₀ s₀') hxs' (run_rounds hRk)
  generalize hy : (TSt.idle s : TSt (sig1 A B) S' A') = y at hJ
  cases hJ with
  | idle s₁ s₂ =>
    have hp'I : p' ∈ i.p.lim := ⟨m, hp'⟩
    have hlen : x.length < p'.length := by
      have h₁ := congrArg List.length (upper_vis hz)
      rw [length_upper_sroundsMoves, length_streamTake] at h₁
      have := length_upper_le_length p'
      omega
    exact ⟨p', hp'I, hI.prefix_of_length_le hx hp'I hlen.le, _, hz'⟩
  | run => cases hy
  | call => cases hy
  | wait => cases hy
  | dead => cases hy
  | stuck => cases hy

/-- Two linked round shapes at stages `n₁ ≤ n`, with as many upper events, share their completed
linked rounds. -/
theorem pre_fixed {s₀ : S} {s₀' : S'}
    (i : DStrategy.InfInteraction (threadS t s₀) (threadS u s₀')) {n₁ n : ℕ} (hn : n₁ ≤ n)
    {rsL₁ rsL : List (A' × List (Call E) × (B' ⊕ PUnit.{u + 1}))} {a' : A'}
    {Q₁ Q : List (Move E (sig1 A' B'))}
    (hp₁ : i.p n₁ = sroundsMoves rsL₁ ++ .inr (.ask a') :: Q₁)
    (hp : i.p n = sroundsMoves rsL ++ .inr (.ask a') :: Q) (hQ₁ : upper Q₁ = [])
    (hQ : upper Q = []) (hU : (upper (i.p n₁)).length = (upper (i.p n)).length) :
    (sroundsMoves rsL : List (Move E (sig1 A' B'))) = sroundsMoves rsL₁ := by
  have h₁ : sroundsMoves rsL₁ ++ [.inr (.ask a')] <+: i.p n :=
    ((hp₁ ▸ ⟨Q₁, by simp⟩ : sroundsMoves rsL₁ ++ [.inr (.ask a')] <+: i.p n₁)).trans
      (i.mono_p.le hn)
  have h₂ : sroundsMoves rsL ++ [.inr (.ask a')] <+: i.p n := hp ▸ ⟨Q, by simp⟩
  rw [hp₁, hp] at hU
  simp [upper_append, hQ₁, hQ] at hU
  exact (eq_of_upper h₁ h₂ hU).1.symm

/-- **The client streams inside a round with infinitely many server calls**: the visible limit
is a linked stream. -/
theorem inf_fwd_clientStream (hnt : NoPlainTrap t) (htd : StoreDet t) {s₀ : S} {s₀' : S'}
    (i : DStrategy.InfInteraction (threadS t s₀) (threadS u s₀')) (hu : i.p.Unbounded)
    (htu : i.t.Unbounded)
    {rs_c : List (A' × List (Call (sig1 A B)) × (B' ⊕ PUnit.{u + 1}))} {s' : S'} {a' : A'}
    {ω : ℕ → Call (sig1 A B)} (hrc : Rounds u s₀' rs_c s') (hω : ω ∈ u.2.2 s' a')
    (hlimt : i.t.lim = streamPlay (sroundsMoves rs_c) a' ω) :
    i.p.lim ∈ (threadS (linkS t u) (s₀, s₀')).inf := by
  obtain ⟨as, r, st, hinf, hlims⟩ := server_coherent htd i htu hlimt
  set N := (rs_c.flatMap fun r => r.2.1).length with hNdef
  have hN : (lower (sroundsMoves rs_c : List (Move (sig1 A B) (sig1 A' B')))).length = 2 * N :=
    length_lower_sroundsMoves rs_c
  set l : ℕ → List (Call E) := fun k => (r (N + k)).1 with hldef
  set C₀ := (sroundsMoves rs_c : List (Move (sig1 A B) (sig1 A' B'))).length
  obtain ⟨n₁, hn₁⟩ := htu (C₀ + 1)
  have hlen₁ : ∀ n, n₁ ≤ n → C₀ < (i.t n).length := fun n hn => by
    have := (i.mono_t.le hn).length_le; omega
  have hst : ∀ n, n₁ ≤ n → ∃ j c z, SRun (linkS t u) (.idle (s₀, s₀')) (i.p n) z ∧
      (∀ k < j, (⟨as (N + k), (r (N + k)).2⟩ : Call (sig1 A B)) = ω k) ∧
      (i.t n).length ≤ C₀ + 2 * j + 2 ∧
      ((z = .run (st N, s') a' (logTake l j ++ c) ∧ c <+: l j) ∨
        ∃ m, z = .wait (st N, s') a' (logTake l j ++ c) m ∧ CallPre c m (l j)) :=
    fun n hn => stage_clientStream hnt htd i hrc hω hlimt hinf hlims hN (hlen₁ n hn)
  -- the visible shape at each late stage
  have hshape : ∀ n, n₁ ≤ n → ∃ rsL j Q, Rounds (linkS t u) (s₀, s₀') rsL (st N, s') ∧
      i.p n = sroundsMoves rsL ++ .inr (.ask a') :: Q ∧ upper Q = [] ∧
      Q <+: callMoves (logTake l (j + 1)) := by
    intro n hn
    obtain ⟨j, c, z, hz, -, -, hform⟩ := hst n hn
    rcases hform with ⟨rfl, hc⟩ | ⟨m, rfl, hc⟩
    · obtain ⟨rsL, hrsL, hp⟩ := shape_inround (T := []) hz (.inl ⟨rfl, rfl⟩)
      refine ⟨rsL, j, _, hrsL, hp, by simp [upper_append], ?_⟩
      rw [List.append_nil, logTake_succ]
      exact callMoves_prefix ((List.prefix_append_right_inj _).2 hc)
    · obtain ⟨rsL, hrsL, hp⟩ := shape_inround hz (.inr ⟨m, rfl, rfl⟩)
      refine ⟨rsL, j, _, hrsL, hp, by simp [upper_append], ?_⟩
      obtain ⟨n', r', hr'⟩ := hc
      rw [logTake_succ]
      show _ <+: callMoves (logTake l j ++ l j)
      rw [hr']
      exact ⟨callMoves r' ++ [] |>.cons (.inl (.ans m n')), by simp⟩
  have hU : ∀ n, n₁ ≤ n → (upper (i.p n)).length = (upper (sroundsMoves rs_c :
      List (Move (sig1 A B) (sig1 A' B')))).length + 1 := fun n hn => by
    rw [upper_vis (i.zip n)]
    obtain ⟨K, hK⟩ : i.t n ∈ streamPlay (sroundsMoves rs_c) a' ω :=
      hlimt ▸ Chain.mem_lim_self _ n
    exact length_upper_inround hK (hlen₁ n hn)
  -- infinitely many server calls
  have hl' : ∀ m, ∃ k, m < (streamTake l k).flatten.length := by
    by_contra hcon
    push Not at hcon
    obtain ⟨m, hm⟩ := hcon
    obtain ⟨rsL₁, -, Q₁, -, hp₁, hQ₁, -⟩ := hshape n₁ le_rfl
    obtain ⟨n, hn, hlen⟩ := i.mono_p.unbounded_ge hu
      ((sroundsMoves rsL₁ : List (Move E (sig1 A' B'))).length + 2 * m + 2) n₁
    obtain ⟨rsL, j, Q, -, hp, hQ, hQb⟩ := hshape n hn
    have hpre := pre_fixed i hn hp₁ hp hQ₁ hQ (by rw [hU n₁ le_rfl, hU n hn])
    have h₁ := hQb.length_le
    have h₂ := hm (j + 1)
    rw [hp, hpre] at hlen
    simp [length_callMoves] at hlen h₁
    simp only [logTake] at h₁
    omega
  -- the coherent service and the linked stream
  have hag : ∀ k, (⟨as (N + k), (r (N + k)).2⟩ : Call (sig1 A B)) = ω k := fun k => by
    obtain ⟨n, hn, hl⟩ := i.mono_t.unbounded_ge htu (C₀ + 2 * (k + 1) + 3) n₁
    obtain ⟨j, c, z, -, hag, hlen, -⟩ := hst n hn
    exact hag k (by omega)
  have hserve : InfServe t (st N, s').1 ω l (fun k => st (N + k)) :=
    ⟨rfl, fun k => by
      have h := hinf.step (N + k)
      rw [← hag k]
      exact h⟩
  have hωE : flatStream l hl' ∈ (linkS t u).2.2 (st N, s') a' :=
    .inr ⟨ω, hω, l, _, hserve, fun m => by obtain ⟨k, hk⟩ := hl' m; exact ⟨k, hk.le⟩,
      fun k => streamTake_flatStream l hl' k⟩
  refine lim_linked_stream i hu hωE (n₁ := n₁) (hU := hU) fun n hn => ?_
  obtain ⟨rsL, j, Q, hrsL, hp, hQ, hQb⟩ := hshape n hn
  refine ⟨rsL, Q, (streamTake l (j + 1)).flatten.length, hrsL, hp, ?_, hQ⟩
  rw [streamTake_flatStream l hl' (j + 1)]
  exact hQb

/-- **The client waits on one call forever**: the server streams inside the served call, and the
visible limit is a linked stream. -/
theorem inf_fwd_serverStream (hnt : NoPlainTrap t) (htd : StoreDet t) {s₀ : S} {s₀' : S'}
    (i : DStrategy.InfInteraction (threadS t s₀) (threadS u s₀')) (hu : i.p.Unbounded)
    (htu : ¬ i.t.Unbounded) : i.p.lim ∈ (threadS (linkS t u) (s₀, s₀')).inf := by
  obtain ⟨B₀, hB₀⟩ : ∃ k, ∀ n, (i.t n).length < k := by
    by_contra h
    push Not at h
    exact htu fun k => let ⟨n, hn⟩ := h k; ⟨n, hn⟩
  obtain ⟨n₀, hn₀⟩ := i.mono_t.eventually_const htu
  have hsu : i.s.Unbounded := i.unbounded_or.resolve_right htu
  rcases (StratSession.mem_inf_iff_of_storeDet htd).1 (i.lim_s hsu) with
    ⟨R_s, s₁, a_s, ω_t, hRs, hωt, hlims⟩ | ⟨as, r, st, -, hlims⟩
  swap
  · exfalso
    obtain ⟨n, hn⟩ := upper_unbounded_of_rounds i.mono_s hsu hlims B₀
    have h₁ := congrArg List.length (upper_eq_lower (i.zip n))
    have h₂ := length_lower_add_upper (i.t n)
    have := hB₀ n
    omega
  obtain ⟨n₁', hn₁'⟩ := hsu ((sroundsMoves R_s : List (Move E (sig1 A B))).length + 1)
  set n₁ := max n₀ n₁'
  have hlen : ∀ n, n₁ ≤ n →
      (sroundsMoves R_s : List (Move E (sig1 A B))).length < (i.s n).length := fun n hn => by
    have := (i.mono_s.le (le_trans (le_max_right n₀ n₁') hn)).length_le; omega
  have hconst : ∀ n, n₁ ≤ n → i.t n = i.t n₀ := fun n hn => hn₀ n (le_trans (le_max_left _ _) hn)
  obtain ⟨y, hy⟩ := mem_plays.1 (i.mem_t n₀)
  have hst := fun n (hn : n₁ ≤ n) =>
    stage_serverStream (u := u) hnt i hRs hωt hlims (hlen n hn) ((hconst n hn).symm ▸ hy)
  obtain ⟨R, rs, σ, a', j₁, z₁, rfl, hRs₁, hR₀, hR, hus, -, -, -⟩ := hst n₁ le_rfl
  -- every late stage runs the same linked round
  have hsame : ∀ n, n₁ ≤ n → ∃ j z, SRun (linkS t u) (.idle (s₀, s₀')) (i.p n) z ∧
      (z = .run σ a' (servedLog rs ++ streamTake ω_t j) ∨
        z = .wait σ a' (servedLog rs ++ streamTake ω_t j) (ω_t j).1) := by
    intro n hn
    obtain ⟨R', rs', σ', a'', j, z, hy', hRs', hR₀', -, -, hz, -, hform⟩ := hst n hn
    simp only [TSt.wait.injEq] at hy'
    obtain ⟨hσ₂, rfl, hsv, -⟩ := hy'
    have hl : rs'.length = rs.length := by
      simpa [served] using congrArg List.length hsv.symm
    rw [hRs₁] at hRs'
    obtain ⟨rfl, rfl⟩ := List.append_inj' hRs' hl.symm
    have hσ : σ' = σ := Prod.ext (rounds_det htd hR₀' hR₀) hσ₂.symm
    subst hσ
    exact ⟨j, z, hz, hform⟩
  have hωE : prependStream (servedLog rs) ω_t ∈ (linkS t u).2.2 σ a' :=
    .inl ⟨rs, s₁, a_s, ω_t, hR, hus, hωt, streamTake_prependStream _ _⟩
  refine lim_linked_stream i hu hωE (n₁ := n₁) (U := (upper (i.t n₀)).length)
    (fun n hn => by rw [upper_vis (i.zip n), hconst n hn]) fun n hn => ?_
  obtain ⟨j, z, hz, hform⟩ := hsame n hn
  rcases hform with rfl | rfl
  · obtain ⟨rsL, hrsL, hp⟩ := shape_inround (T := []) hz (.inl ⟨rfl, rfl⟩)
    refine ⟨rsL, _, (servedLog rs).length + j, hrsL, hp, ?_, by simp [upper_append]⟩
    rw [streamTake_prependStream, List.append_nil]
    exact List.prefix_refl _
  · obtain ⟨rsL, hrsL, hp⟩ := shape_inround hz (.inr ⟨_, rfl, rfl⟩)
    refine ⟨rsL, _, (servedLog rs).length + (j + 1), hrsL, hp, ?_, by simp [upper_append]⟩
    rw [streamTake_prependStream, streamTake_succ, ← List.append_assoc]
    exact ⟨[(Sum.inl (Ev.ans (ω_t j).1 (ω_t j).2) : Move E (sig1 A' B'))], by simp⟩

/-- **Forward**: every infinite play of the composite is one of the linked session. -/
theorem inf_fwd (hnt : NoPlainTrap t) (htd : StoreDet t) {s₀ : S} {s₀' : S'}
    {I : Set (List (Move E (sig1 A' B')))}
    (hI : I ∈ ((threadS t s₀).comp (threadS u s₀')).inf) :
    I ∈ (threadS (linkS t u) (s₀, s₀')).inf := by
  obtain ⟨i, hu, rfl⟩ := hI
  by_cases htu : i.t.Unbounded
  · rcases StratSession.mem_inf_iff.1 (i.lim_t htu) with ⟨rs_c, s', a', ω, hrc, hω, hlimt⟩ |
        ⟨ac, rc, hlimt, hR⟩
    · exact inf_fwd_clientStream hnt htd i hu htu hrc hω hlimt
    · exact inf_fwd_rounds hnt i hu hlimt hR
  · exact inf_fwd_serverStream hnt htd i hu htu

/-- **Forward**: every divergence of the composite is one of the linked session. -/
theorem div_fwd (hnt : NoPlainTrap t) (htd : StoreDet t) {s₀ : S} {s₀' : S'}
    {p : List (Move E (sig1 A' B'))} (hp : p ∈ ((threadS t s₀).comp (threadS u s₀')).div) :
    p ∈ (threadS (linkS t u) (s₀, s₀')).div := by
  rcases hp with ⟨sv, cv, hz, h⟩ | ⟨i, hi⟩
  · exact div_fwd_local hnt hz h
  · exact chatter_fwd hnt htd i hi

/-- **Linking is composition with hiding**: for a server without plain traps, store-deterministic,
and a store-deterministic linked triple, the composite of the sessions is the linked session. -/
theorem comp_threadS (hnt : NoPlainTrap t) (htd : StoreDet t) (hL : StoreDet (linkS t u))
    (s₀ : S) (s₀' : S') :
    (threadS t s₀).comp (threadS u s₀') = threadS (linkS t u) (s₀, s₀') :=
  DStrategy.ext (Strategy.ext fun _ => mem_comp_iff hnt)
    (Set.ext fun _ => ⟨div_fwd hnt htd, div_bwd⟩) (Set.ext fun _ => ⟨inf_fwd hnt htd, inf_bwd hL⟩)

end Silmaril.Proofs.Games.Abstract.SessionLink
