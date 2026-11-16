module

public import Silmaril.Proofs.Games.Abstract.SessionHost.Plays
public import Silmaril.Games.DivComp.Thms
import Mathlib.Data.List.Induction

/-!
# Divergence of a session with host imports (proofs)

The composite of the host beside copycat and the session of `t` diverges exactly where the linked
session does.

* **Local divergence**: a divergence of the session of `t` with allowed host answers is a linked
  behaviour `div`; the host diverging at a call is a linked host divergence (`div_fwd`).
* **Chatter** (`chatter`): an infinite interaction with a constant visible part `q`. The session
  moves forever (the host moves only visibly or in synchrony), so its limit is an infinite play of
  the session (`StratSession.mem_inf_iff`). Every visible part is `q` up to one forwarded move,
  so it cannot complete infinitely many rounds: it is a productive stream after completed rounds
  with boundedly many, hence finitely many, component calls. That is a linked chatter divergence,
  at the visible part of the stream after its last component call; and `q` is that visible part,
  since it ends with neither a pending component call nor a forwarded answer.
* Conversely (`div_bwd`) a linked divergence is built from the end as for finite plays
  (`SessionHost.Plays.bwd`); for chatter the session of `t` continues along the stream with hidden
  host calls only.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionHost

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.SessionHost
  Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread
  Silmaril.Games.Abstract.StratSession

universe u

variable {E F : Sig.{u}} {S A B : Type u} {R : HostRel E}

/-! ## Lists, rounds and runs -/

section Lists

theorem exists_stable (f : ℕ → ℕ) (hf : Monotone f) (N : ℕ) (hb : ∀ k, f k ≤ N) :
    ∃ n, ∀ k, n ≤ k → f k = f n := by
  by_contra h
  simp only [not_exists, not_forall] at h
  have : ∀ j, ∃ n, j ≤ f n := by
    intro j
    induction j with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ j ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨k, hk, hne⟩ := h n
      exact ⟨k, by have := hf hk; omega⟩
  obtain ⟨n, hn⟩ := this (N + 1)
  have := hb n; omega

theorem fCalls_streamTake_succ (ω : ℕ → Call (E ⊕ₛ F)) (k : ℕ) :
    fCalls (streamTake ω (k + 1)) = fCalls (streamTake ω k) ++ fCall (ω k) := by
  rw [streamTake_succ', fCalls_append]; exact congrArg _ (List.append_nil _)


/-- A stream with only host calls after `n₀` has constant component calls after `n₀`. -/
theorem fCalls_stable {ω : ℕ → Call (E ⊕ₛ F)} {n₀ : ℕ} (h : ∀ k, n₀ ≤ k → fCall (ω k) = [])
    (k : ℕ) : fCalls (streamTake ω (n₀ + k)) = fCalls (streamTake ω n₀) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, fCalls_streamTake_succ, ih, h _ (Nat.le_add_right _ _),
      List.append_nil]

/-- Boundedly many component calls in a stream: only host calls from some point on. -/
theorem exists_fCall_nil {ω : ℕ → Call (E ⊕ₛ F)} {N : ℕ}
    (hb : ∀ k, (fCalls (streamTake ω k)).length ≤ N) : ∃ n₀, ∀ k, n₀ ≤ k → fCall (ω k) = [] := by
  have hm : Monotone fun k => (fCalls (streamTake ω k)).length :=
    monotone_nat_of_le_succ fun k => (fCalls_prefix (streamTake_mono ω (Nat.le_succ k))).length_le
  obtain ⟨n₀, hn⟩ := exists_stable _ hm N hb
  refine ⟨n₀, fun k hk => ?_⟩
  have h₁ := hn k hk
  have h₂ := hn (k + 1) (Nat.le_succ_of_le hk)
  simp only [fCalls_streamTake_succ, List.length_append] at h₂
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem ends_ask_of_wait {X G : Sig.{u}} {v : List (Move X G)} {g : G.Op} {μ : X.Op}
    (h : Path .idle v (.wait g μ)) : ∃ W, v = W ++ [.inl (.ask μ)] := by
  rcases List.eq_nil_or_concat v with rfl | ⟨W, o, rfl⟩
  · cases h
  · rw [List.concat_eq_append] at h
    obtain ⟨x, -, hs⟩ := Path.concat_iff.1 h
    cases hs
    exact ⟨W, List.concat_eq_append⟩

theorem trun_snoc {X : Sig.{u}} {B' : Type u} {f : AFun X S A B'} {P : Pending X S A}
    {x z : TSt X S A} {p : List (Move X (sig1 A B'))} {o : Move X (sig1 A B')}
    (h : TRun f P x (p ++ [o]) z) : ∃ y, TRun f P x p y ∧ TStep f P y o z := by
  obtain ⟨y, h₁, h₂⟩ := h.of_append
  cases h₂ with
  | cons hs hn => cases hn; exact ⟨y, h₁, hs⟩

/-- **A run to a running state** is completed rounds, the question, and the calls. -/
theorem run_split {X : Sig.{u}} {B' : Type u} {f : AFun X S A B'} {P : Pending X S A} {s₀ s : S}
    {a : A} : ∀ {c : List (Call X)} {p : List (Move X (sig1 A B'))},
      TRun f P (.idle s₀) p (.run s a c) →
      ∃ pre, TRun f P (.idle s₀) pre (.idle s) ∧ p = pre ++ .inr (.ask a) :: callMoves c := by
  intro c
  induction c using List.reverseRecOn with
  | nil =>
    intro p hp
    rcases List.eq_nil_or_concat p with rfl | ⟨p', o, rfl⟩
    · cases hp
    · rw [List.concat_eq_append] at hp ⊢
      obtain ⟨y, h₁, h₂⟩ := trun_snoc hp
      generalize hY : (TSt.run s a [] : TSt X S A) = Y at h₂
      cases h₂ with
      | ask => cases hY; exact ⟨p', h₁, rfl⟩
      | reply => simp at hY
      | call => cases hY
      | ret => cases hY
      | trap => cases hY
      | deadAsk => cases hY
  | append_singleton c x ih =>
    intro p hp
    rcases List.eq_nil_or_concat p with rfl | ⟨p', o, rfl⟩
    · cases hp
    · rw [List.concat_eq_append] at hp ⊢
      obtain ⟨y, h₁, h₂⟩ := trun_snoc hp
      generalize hY : (TSt.run s a (c ++ [x]) : TSt X S A) = Y at h₂
      cases h₂ with
      | ask => simp at hY
      | reply s' a' c' m n =>
        rcases List.eq_nil_or_concat p' with rfl | ⟨p'', o', rfl⟩
        · cases h₁
        · rw [List.concat_eq_append] at h₁ ⊢
          obtain ⟨y', h₃, h₄⟩ := trun_snoc h₁
          generalize hW : (TSt.wait s' a' c' m : TSt X S A) = W at h₄
          cases h₄ with
          | call =>
            simp only [TSt.wait.injEq] at hW
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
            simp only [TSt.run.injEq] at hY
            obtain ⟨rfl, rfl, hc⟩ := hY
            obtain ⟨rfl, rfl⟩ := eq_of_snoc_eq hc
            obtain ⟨pre, hpre, rfl⟩ := ih h₃
            exact ⟨pre, hpre, by simp⟩
          | ask => cases hW
          | reply => cases hW
          | ret => cases hW
          | trap => cases hW
          | deadAsk => cases hW
      | call => cases hY
      | ret => cases hY
      | trap => cases hY
      | deadAsk => cases hY

end Lists

section Rounds

variable {X G : Sig.{u}}

/-- The rounds seen from the linked side: logs reduced to their component calls. -/
def projR {Y : Type u} (rs : List (A × List (Call (E ⊕ₛ F)) × Y)) : List (A × List (Call F) × Y) :=
  rs.map fun r => (r.1, fCalls r.2.1, r.2.2)

theorem vis_sroundsMoves (rs : List (A × List (Call (E ⊕ₛ F)) × (B ⊕ PUnit.{u + 1}))) :
    vis (sroundsMoves rs) = sroundsMoves (projR rs) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [sroundsMoves, List.flatMap_cons, vis_append, projR, List.map_cons] at ih ⊢
    rw [ih]
    simp [sroundMoves, visMove, vis_callMoves]

theorem map_relMove_callMoves (c : List (Call X)) :
    (callMoves c : List (Move X (sig1 A (B ⊕ PUnit.{u + 1})))).map relMove = callMoves c := by
  induction c with
  | nil => rfl
  | cons x c ih => simp only [callMoves_cons', List.map_cons, ih]; rfl

theorem map_relMove_roundsMoves (rs : List (A × List (Call X) × (B ⊕ PUnit.{u + 1}))) :
    (roundsMoves rs).map relMove = sroundsMoves rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [roundsMoves, sroundsMoves, List.flatMap_cons, List.map_append] at ih ⊢
    rw [ih]
    simp only [roundMoves, sroundMoves, List.map_cons, List.map_append, map_relMove_callMoves]
    rfl

theorem two_mul_le_sroundsMoves (rs : List (A × List (Call X) × (B ⊕ PUnit.{u + 1}))) :
    2 * rs.length ≤ (sroundsMoves rs).length := by
  induction rs with
  | nil => exact le_rfl
  | cons r rs ih =>
    simp only [sroundsMoves, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    simp only [sroundMoves, List.length_cons, List.length_append]
    omega

theorem ok_of_okV_sroundsMoves {rs : List (A × List (Call (E ⊕ₛ F)) × (B ⊕ PUnit.{u + 1}))}
    (h : OkV R (sroundsMoves rs : List (Move (E ⊕ₛ F) (sig1 A B)))) : ∀ r ∈ rs, Ok R F r.2.1 := by
  intro r hr
  refine ok_of_okV_callMoves (G := sig1 A B) fun o ho => h o ?_
  exact List.mem_flatMap.2 ⟨r, hr, List.mem_cons_of_mem _ (List.mem_append_left _ ho)⟩

theorem okV_sroundsMoves {rs : List (A × List (Call (E ⊕ₛ F)) × (B ⊕ PUnit.{u + 1}))}
    (h : ∀ r ∈ rs, Ok R F r.2.1) : OkV R (sroundsMoves rs : List (Move (E ⊕ₛ F) (sig1 A B))) := by
  intro o ho
  obtain ⟨r, hr, ho⟩ := List.mem_flatMap.1 ho
  simp only [sroundMoves, List.mem_cons, List.mem_append] at ho
  rcases ho with rfl | ho | rfl | ho
  · trivial
  · exact okV_callMoves (h r hr) o ho
  · trivial
  · cases ho

variable {t : ObsTriple (E ⊕ₛ F) S A (B ⊕ PUnit.{u + 1})}

theorem rounds_proj {s s' : S} {rs : List (A × List (Call (E ⊕ₛ F)) × (B ⊕ PUnit.{u + 1}))}
    (h : Rounds t s rs s') (hok : ∀ r ∈ rs, Ok R F r.2.1) :
    Rounds (hostLinkS R t) s (projR rs) s' := by
  induction h with
  | nil => exact .nil _
  | cons hc _ ih =>
    exact .cons (.inl ⟨_, hc, hok _ (.head _), rfl⟩) (ih fun r hr => hok r (.tail _ hr))

theorem rounds_lift {s s' : S} {rs' : List (A × List (Call F) × (B ⊕ PUnit.{u + 1}))}
    (h : Rounds (hostLinkS R t) s rs' s') :
    ∃ rs, Rounds t s rs s' ∧ projR rs = rs' ∧ ∀ r ∈ rs, Ok R F r.2.1 := by
  induction h with
  | nil => exact ⟨[], .nil _, rfl, fun _ h => nomatch h⟩
  | cons hc _ ih =>
    obtain ⟨rs, hrs, rfl, hok⟩ := ih
    rcases hc with ⟨c, hc, hokc, rfl⟩ | ⟨hd, -⟩
    · exact ⟨_ :: rs, .cons hc hrs, rfl, fun r hr => (List.mem_cons.1 hr).elim (· ▸ hokc) (hok r)⟩
    · cases hd

/-- A reached allowed log has its component calls reached by the linked automaton. -/
theorem reachL {s : S} {a : A} {c : List (Call (E ⊕ₛ F))} (hr : Reach t s a c) (hc : Ok R F c) :
    ∀ c₀ m, CallPre c₀ m ([] ++ fCalls c) → (c₀, m) ∈ satP (hostLinkS R t) s a := by
  intro c₀ m h
  rw [List.nil_append] at h
  obtain ⟨c₁, h₁, h₂, rfl⟩ := lift_callPre hr hc h
  exact .inl ⟨c₁, h₁, h₂, rfl⟩

end Rounds

/-! ## A stage of an interaction -/

variable {t : ObsTriple (E ⊕ₛ F) S A (B ⊕ PUnit.{u + 1})} {s₀ : S}

/-- **A stage of an interaction**: allowed host answers, and the visible part up to one
forwarded move. -/
theorem stage {sH : List (Move F (E ⊕ₛ F))} {v : List (Move (E ⊕ₛ F) (sig1 A B))}
    {q : List (Move F (sig1 A B))} (hs : sH ∈ (hostCopy F R).toStrategy)
    (hv : v ∈ (threadS t s₀).toStrategy) (hz : Zip sH v q) :
    OkV R v ∧ ∃ h g, Path .idle v g ∧ Compat h g ∧ q ++ aOf h = vis v ++ bOf h := by
  obtain ⟨h, hr⟩ := hs
  obtain ⟨g, hg⟩ := (threadS t s₀).toStrategy.legal hv
  obtain ⟨hc, hok, he⟩ := zip_fwd hz hr hg Compat.idle
  exact ⟨hok, h, g, hg, hc, by simpa [aOf, bOf] using he⟩

theorem stage_length {h : HSt E F} {q : List (Move F (sig1 A B))}
    {V : List (Move F (sig1 A B))} (he : q ++ aOf h = V ++ bOf h) :
    V.length ≤ q.length + 1 ∧ q.length ≤ V.length + 1 := by
  have := congrArg List.length he
  have := length_aOf_le (G := sig1 A B) h
  have := length_bOf_le (G := sig1 A B) h
  simp only [List.length_append] at *
  omega

/-- A visible part ending with neither a pending component call nor a forwarded answer. -/
theorem eq_of_stage {v : List (Move (E ⊕ₛ F) (sig1 A B))} {q V : List (Move F (sig1 A B))}
    {h : HSt E F} {g : Pos (E ⊕ₛ F) (sig1 A B)} (hV : ∀ W m, V ≠ W ++ [.inl (.ask m)])
    (hvV : vis v = V) (hg : Path .idle v g) (hc : Compat h g)
    (he : q ++ aOf h = vis v ++ bOf h) : q = V := by
  rw [hvV] at he
  cases h with
  | idle => simpa [aOf, bOf] using he
  | waitE m => simpa [aOf, bOf] using he
  | waitF m => simpa [aOf, bOf] using he
  | askF m => exact absurd he.symm (by simpa [aOf, bOf] using hV q m)
  | ansF m n =>
    cases hc with
    | ansF g' _ _ =>
      obtain ⟨W, rfl⟩ := ends_ask_of_wait hg
      exact absurd (by rw [← hvV, vis_append]; rfl) (hV (vis W) m)

theorem not_ask_end {X : Sig.{u}} (rs : List (A × List (Call X) × (B ⊕ PUnit.{u + 1}))) (a : A)
    (c : List (Call X)) :
    ∀ (W : List (Move X (sig1 A B))) (m : X.Op),
      sroundsMoves rs ++ .inr (.ask a) :: callMoves c ≠ W ++ [.inl (.ask m)] := by
  intro W m h
  rcases List.eq_nil_or_concat c with rfl | ⟨c₀, x, rfl⟩
  · rw [callMoves_nil', ← List.singleton_append, List.append_nil] at h
    exact nomatch (eq_of_snoc_eq h).2
  · have h' : (sroundsMoves rs ++ .inr (.ask a) :: callMoves c₀ ++ [.inl (.ask x.1)]) ++
        [.inl (.ans x.1 x.2)] = W ++ [.inl (.ask m)] := by
      rw [← h, List.concat_eq_append, callMoves_append']; simp
    exact nomatch (eq_of_snoc_eq h').2

/-! ## The forward direction -/

/-- The plays of a productive stream after completed session rounds. -/
abbrev sPlay {X : Sig.{u}} (rs : List (A × List (Call X) × (B ⊕ PUnit.{u + 1}))) (a : A)
    (ω : ℕ → Call X) (k : ℕ) : List (Move X (sig1 A B)) :=
  sroundsMoves rs ++ .inr (.ask a) :: callMoves (streamTake ω k)

theorem sPlay_mono {X : Sig.{u}} (rs : List (A × List (Call X) × (B ⊕ PUnit.{u + 1}))) (a : A)
    (ω : ℕ → Call X) {j k : ℕ} (h : j ≤ k) : sPlay rs a ω j <+: sPlay rs a ω k := by
  obtain ⟨u, hu⟩ := streamTake_mono ω h
  exact ⟨callMoves u, by simp [sPlay, ← hu]⟩

theorem vis_sPlay (rs : List (A × List (Call (E ⊕ₛ F)) × (B ⊕ PUnit.{u + 1}))) (a : A)
    (ω : ℕ → Call (E ⊕ₛ F)) (k : ℕ) :
    vis (sPlay rs a ω k) =
      sroundsMoves (projR rs) ++ .inr (.ask a) :: callMoves (fCalls (streamTake ω k)) := by
  simp [sPlay, vis_sroundsMoves, visMove, vis_callMoves]

/-- **Divergence from chatter.** -/
theorem chatter (i : DStrategy.InfInteraction (hostCopy F R) (threadS t s₀))
    {q : List (Move F (sig1 A B))} (hi : ∀ n, i.p n = q) :
    q ∈ (threadS (hostLinkS R t) s₀).div := by
  have hst := fun n => stage (i.mem_s n) (i.mem_t n) (i.zip n)
  have hlen : ∀ n, (vis (i.t n)).length ≤ q.length + 1 := fun n => by
    obtain ⟨-, h, g, -, -, he⟩ := hst n
    rw [hi n] at he
    exact (stage_length he).1
  obtain ⟨-, hu, -, hlim⟩ := i.chatter_inf hi
  rcases mem_inf_iff.1 hlim with ⟨rs, s, a, ω, hrs, hω, hI⟩ | ⟨a, r, hI, -⟩
  · -- a productive stream after completed rounds
    have hP : ∀ k, ∃ n, sPlay rs a ω k <+: i.t n := fun k => by
      have : sPlay rs a ω k ∈ i.t.lim := hI ▸ ⟨k, List.prefix_refl _⟩
      exact this
    have hokP : ∀ k, OkV R (sPlay rs a ω k) := fun k => by
      obtain ⟨n, hn⟩ := hP k; exact (hst n).1.of_prefix hn
    have hokrs : ∀ r ∈ rs, Ok R F r.2.1 :=
      ok_of_okV_sroundsMoves ((hokP 0).of_prefix (List.prefix_append _ _))
    have hokω : ∀ k, Ok R F (streamTake ω k) := fun k =>
      ok_of_okV_callMoves (G := sig1 A B) fun o ho => hokP k o
        (List.mem_append_right _ (List.mem_cons_of_mem _ ho))
    have hall : ∀ k, sumL R F (ω k).1 (.answer (ω k).2) := fun k =>
      hokω (k + 1) (ω k) (by rw [streamTake_succ']; simp)
    have hbound : ∀ k, (fCalls (streamTake ω k)).length ≤ q.length + 1 := fun k => by
      obtain ⟨n, hn⟩ := hP k
      have h₁ := (vis_prefix hn).length_le
      rw [vis_sPlay] at h₁
      have := hlen n
      simp only [List.length_append, List.length_cons, length_callMoves'] at h₁
      omega
    obtain ⟨n₀, hn₀⟩ := exists_fCall_nil hbound
    have hstab := fCalls_stable hn₀
    set c := fCalls (streamTake ω n₀)
    set V := vis (sPlay rs a ω n₀)
    have hV : V = sroundsMoves (projR rs) ++ .inr (.ask a) :: callMoves c := vis_sPlay rs a ω n₀
    -- the visible part of a late stage is `V`
    obtain ⟨n, hn⟩ := hP n₀
    have hvn : vis (i.t n) = V := by
      obtain ⟨k, hk⟩ : i.t n ∈ streamPlay (sroundsMoves rs) a ω := hI ▸ Chain.mem_lim_self _ n
      have h₁ : vis (i.t n) <+: vis (sPlay rs a ω (n₀ + k)) :=
        vis_prefix (hk.trans (sPlay_mono rs a ω (Nat.le_add_left _ _)))
      rw [vis_sPlay, hstab, ← hV] at h₁
      exact h₁.eq_of_length (le_antisymm h₁.length_le (vis_prefix hn).length_le)
    obtain ⟨-, h, g, hg, hc, he⟩ := hst n
    rw [hi n] at he
    have hq : q = V := eq_of_stage (hV ▸ not_ask_end _ a c) hvn hg hc he
    -- the linked run
    have hrun : TRun (hostLinkS R t).1 (satP (hostLinkS R t)) (.idle s₀)
        (roundsMoves (projR rs) ++ .inr (.ask a) :: callMoves c) (.run s a c) := by
      have h₁ := run_idle_iff.2 ⟨projR rs, rfl, rounds_proj hrs hokrs⟩
      have h₂ := run_callMoves (f := (hostLinkS R t).1) (P := satP (hostLinkS R t)) (s := s)
        (a := a) c (c₀ := []) (reachL (reach_of_stream hω n₀) (hokω n₀))
      rw [List.nil_append] at h₂
      exact h₁.append (.cons (.ask s a) h₂)
    refine ⟨_, ⟨s, a, c, hrun, .inr ⟨rfl, .inr ⟨ω, ⟨hω, hall⟩, n₀, hn₀, rfl⟩⟩⟩, ?_⟩
    rw [hq, hV, List.map_append, map_relMove_roundsMoves, List.map_cons,
      map_relMove_callMoves]
    rfl
  · -- infinitely many rounds: the visible part would grow
    exfalso
    have hX : sroundsMoves (streamTake (fun i => (a i, r i)) (q.length + 1)) ∈ i.t.lim :=
      hI ▸ Chain.mem_lim_self _ _
    obtain ⟨n, hn⟩ := hX
    have h₁ := (vis_prefix hn).length_le
    rw [vis_sroundsMoves] at h₁
    have h₂ := two_mul_le_sroundsMoves (projR (streamTake (fun i => (a i, r i)) (q.length + 1)))
    have h₃ : (projR (streamTake (fun i => (a i, r i)) (q.length + 1))).length = q.length + 1 := by
      simp [projR]
    have := hlen n
    omega

theorem div_fwd {q : List (Move F (sig1 A B))}
    (hq : q ∈ ((hostCopy F R).comp (threadS t s₀)).div) :
    q ∈ (threadS (hostLinkS R t) s₀).div := by
  rcases hq with ⟨sH, v, hz, ⟨⟨m, hrH, hd⟩, hv⟩ | ⟨hH, hv⟩⟩ | ⟨i, hi⟩
  · obtain ⟨p, x, y, hT, rfl, hy, hJ, hvv, hpath⟩ := fwd_play hv ((stage ⟨_, hrH⟩ hv hz).1)
    obtain ⟨hc, -, he⟩ := zip_fwd hz hrH hpath Compat.idle
    simp only [aOf, bOf, List.nil_append, List.append_nil] at he
    generalize hX : relPos x.pos = X at hc
    cases hc with
    | waitE g _ =>
      cases x <;> simp [TSt.pos, relPos] at hX
      obtain ⟨rfl, rfl⟩ := hX
      cases hJ with
      | waitE _ _ _ _ hok hP =>
        exact ⟨_, ⟨_, _, _, hy, .inr ⟨rfl, .inl ⟨_, m, hP, hok, hd, rfl⟩⟩⟩, by rw [he, hvv]⟩
  · obtain ⟨p, ⟨s, a, c, hT, hcd⟩, rfl⟩ := hv
    obtain ⟨hok, -⟩ := stage hH ⟨p, ⟨_, hT⟩, rfl⟩ hz
    obtain ⟨h, hrH⟩ := hH
    obtain ⟨y, hy, hJ⟩ := fwd hT (okV_map_relMove.1 hok) (J.idle s₀)
    obtain ⟨hc, -, he⟩ := zip_fwd hz hrH (relPath hT.pos) Compat.idle
    cases hc
    simp only [aOf, bOf, List.nil_append, List.append_nil] at he
    cases hJ with
    | run _ _ _ hokc =>
      exact ⟨_, ⟨s, a, _, hy, .inl ⟨c, hcd, hokc, rfl⟩⟩, by rw [he, vis_map_relMove]⟩
  · exact chatter i hi

/-! ## The backward direction -/

theorem div_bwd {q : List (Move F (sig1 A B))} (hq : q ∈ (threadS (hostLinkS R t) s₀).div) :
    q ∈ ((hostCopy F R).comp (threadS t s₀)).div := by
  obtain ⟨q₁, ⟨s, a, c', hy, hd⟩, rfl⟩ := hq
  rcases hd with ⟨c, hc, hok, rfl⟩ | ⟨-, ⟨c, m, hP, hok, hdv, rfl⟩ | ⟨ω, hω, n₀, hn₀, rfl⟩⟩
  · obtain ⟨x, p, hK, hT, rfl, hokp⟩ := bwd hy (K.run s a _ c hok (reach_of_beh hc) rfl)
    cases hK
    obtain ⟨hv, hh, hz⟩ := interaction_of_run hT hokp
    exact DStrategy.mem_div_comp_of_right hh ⟨p, ⟨s, a, c, hT, hc⟩, rfl⟩ hz
  · obtain ⟨x, p, hK, hT, rfl, hokp⟩ := bwd hy (K.run s a _ c hok (reach_of_satP hP) rfl)
    cases hK
    let o : Move (E ⊕ₛ F) (sig1 A (B ⊕ PUnit.{u + 1})) := .inl (.ask (.inl m))
    have hT' : TRun t.1 (satP t) (.idle s₀) (p ++ [o]) (.wait s a c (.inl m)) :=
      hT.append (.cons (.call s a c (.inl m) hP) (.nil _))
    have hokp' : OkV R (p ++ [o]) := okV_append.2 ⟨hokp, okV_cons.2 ⟨trivial, OkV.nil⟩⟩
    obtain ⟨hv, -, hz⟩ := interaction_of_run hT' hokp'
    have hH : hmv ((p ++ [o]).map relMove) ∈ (hostCopy F R).div :=
      ⟨m, hrun_hmv (relPath hT'.pos) (okV_map_relMove.2 hokp'), hdv⟩
    refine DStrategy.mem_div_comp_of_left hH hv ?_
    have : vis (p ++ [o]) = vis p := by
      rw [vis_append]; exact List.append_nil _
    rwa [this] at hz
  · obtain ⟨x, p, hK, hT, rfl, hokp⟩ :=
      bwd hy (K.run s a _ _ (hostObsInf_consistent hω n₀) (reach_of_stream hω.1 n₀) rfl)
    cases hK
    obtain ⟨pre, hpre, rfl⟩ := run_split hT
    obtain ⟨rs, rfl, hrs⟩ := run_idle_iff.1 hpre
    have hokpre : OkV R (roundsMoves rs) := hokp.of_prefix (List.prefix_append _ _)
    let pk : ℕ → List (Move (E ⊕ₛ F) (sig1 A (B ⊕ PUnit.{u + 1}))) := fun k =>
      roundsMoves rs ++ .inr (.ask a) :: callMoves (streamTake ω (n₀ + k))
    have hTk : ∀ k, TRun t.1 (satP t) (.idle s₀) (pk k) (.run s a (streamTake ω (n₀ + k))) := by
      intro k
      have h₂ := run_callMoves (f := t.1) (P := satP t) (s := s) (a := a)
        (streamTake ω (n₀ + k)) (c₀ := []) (by rw [List.nil_append]; exact reach_of_stream hω.1 _)
      rw [List.nil_append] at h₂
      exact hpre.append (.cons (.ask s a) h₂)
    have hokk : ∀ k, OkV R (pk k) := fun k =>
      okV_append.2 ⟨hokpre, okV_cons.2 ⟨trivial, okV_callMoves (hostObsInf_consistent hω _)⟩⟩
    have hvis : ∀ k, (vis (pk k)).map relMove =
        (vis (roundsMoves rs ++ .inr (.ask a) :: callMoves (streamTake ω n₀))).map relMove := by
      intro k
      simp only [pk, vis_append, vis_cons, vis_callMoves, fCalls_stable hn₀]
    have hI := fun k => interaction_of_run (hTk k) (hokk k)
    have hmono : ∀ k, pk k <+: pk (k + 1) := fun k => by
      obtain ⟨u, hu⟩ := streamTake_mono ω (Nat.le_succ (n₀ + k))
      refine ⟨callMoves u, ?_⟩
      show _ = roundsMoves rs ++ .inr (.ask a) :: callMoves (streamTake ω (n₀ + k + 1))
      rw [← hu]; simp [pk]
    have mono_t : Chain.Mono fun k => (pk k).map relMove := fun k => (hmono k).map _
    have mono_s : Chain.Mono fun k => hmv ((pk k).map relMove) := fun k => hmv_prefix (mono_t k)
    have hlim : Chain.lim (fun k => (pk k).map relMove) = streamPlay (sroundsMoves rs) a ω := by
      have heq : ∀ k, (pk k).map relMove = sPlay rs a ω (n₀ + k) := fun k => by
        simp only [pk, sPlay, List.map_append, map_relMove_roundsMoves, List.map_cons,
          map_relMove_callMoves]
        rfl
      refine Chain.lim_eq_of (fun k => ⟨n₀ + k, by rw [heq]; exact List.prefix_refl _⟩)
        (fun k => ⟨k, by rw [heq]; exact sPlay_mono rs a ω (Nat.le_add_left _ _)⟩)
    let i : DStrategy.InfInteraction (hostCopy F R) (threadS t s₀) :=
      { s := fun k => hmv ((pk k).map relMove)
        t := fun k => (pk k).map relMove
        p := fun _ => (vis (roundsMoves rs ++ .inr (.ask a) ::
          callMoves (streamTake ω n₀))).map relMove
        zip := fun k => by
          have := (hI k).2.2; rwa [hvis k] at this
        mem_s := fun k => (hI k).2.1
        mem_t := fun k => (hI k).1
        mono_s := mono_s
        mono_t := mono_t
        mono_p := fun _ => List.prefix_refl _
        unbounded := fun k => ⟨k, by
          simp only [pk, List.length_map, List.length_append, List.length_cons,
            length_callMoves', length_streamTake']; omega⟩
        lim_s := fun hu => ⟨Chain.isInfPlay_lim mono_s hu, fun _ ⟨n, hx⟩ =>
          (hostCopy F R).toStrategy.of_prefix (hI n).2.1 hx⟩
        lim_t := fun _ => hlim ▸ mem_inf.2 ⟨s, hrs, hω.1⟩ }
    exact .inr ⟨i, fun _ => rfl⟩

/-- **The divergences of the composite are those of the linked session.** -/
theorem comp_div : ((hostCopy F R).comp (threadS t s₀)).div = (threadS (hostLinkS R t) s₀).div :=
  Set.ext fun _ => ⟨div_fwd, div_bwd⟩

end Silmaril.Proofs.Games.Abstract.SessionHost
