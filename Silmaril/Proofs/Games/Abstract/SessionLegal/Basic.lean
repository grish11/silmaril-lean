module

public import Silmaril.Games.Abstract.SessionLegal.Defs
public import Silmaril.Games.Abstract.StratObs.Thms
public import Silmaril.Games.Abstract.StratSession.Thms

/-!
# Store-dependent legality of import answers in a session (proofs)

See `Silmaril.Games.Abstract.SessionLegal.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLegal

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
open Silmaril.Games.Abstract.SessionLegal

universe u

variable {E : Sig.{u}} {S A B : Type u} {Lg : S → A → List (Call E) → Prop}

/-! ## Call prefixes -/

section Pending

variable {t : ObsTriple E S A B}

theorem satP_satP {s : S} {a : A} {x : List (Call E) × E.Op} {d : List (Call E)} {m' : E.Op}
    (hd : (d, m') ∈ satP t s a) (hp : CallPre x.1 x.2 d) : x ∈ satP t s a := by
  have h : satP (sat t) s a = satP t s a := by
    have := congrArg (fun t : ObsTriple E S A B => t.2.1) (sat_idem (t := t))
    exact congrFun (congrFun this s) a
  rw [← h]
  exact .inr (.inl ⟨d, m', hd, hp⟩)

theorem lg_of_callPre (hL : PrefixClosed Lg) {s : S} {a : A} {c d : List (Call E)} {m : E.Op}
    (hp : CallPre c m d) (h : Lg s a d) : Lg s a c := by
  obtain ⟨n, c', rfl⟩ := hp
  exact hL s a c _ h

/-- **The call prefixes of the legal part** are the legal call prefixes. -/
theorem satP_restrictLog (hL : PrefixClosed Lg) (s : S) (a : A) :
    satP (restrictLog Lg t) s a = {x | x ∈ satP t s a ∧ Lg s a x.1} := by
  ext x
  constructor
  · rintro (h | ⟨d, m', hd, hp⟩ | ⟨d, e, hd, hp⟩ | ⟨ω, hω, k, hk, hm⟩)
    · exact h
    · exact ⟨satP_satP hd.1 hp, lg_of_callPre hL hp hd.2⟩
    · exact ⟨.inr (.inr (.inl ⟨d, e, hd.1, hp⟩)), lg_of_callPre hL hp hd.2⟩
    · exact ⟨.inr (.inr (.inr ⟨ω, hω.1, k, hk, hm⟩)), hk ▸ hω.2 k⟩
  · exact fun h => .inl h

end Pending

/-! ## Runs of the threading automaton -/

section Runs

variable {B' : Type u} {t : ObsTriple E S A B'}

theorem tstep_mono (hL : PrefixClosed Lg) {x y : TSt E S A} {o : Move E (sig1 A B')}
    (h : TStep (restrictLog Lg t).1 (satP (restrictLog Lg t)) x o y) :
    TStep t.1 (satP t) x o y := by
  cases h with
  | ask => exact .ask _ _
  | call s a c m hm => exact .call s a c m ((satP_restrictLog hL s a ▸ hm).1)
  | reply => exact .reply _ _ _ _ _
  | ret s a c b s' hb => exact .ret s a c b s' hb.1
  | trap s a c hb => exact .trap s a c hb.1
  | deadAsk => exact .deadAsk _

/-- Runs of the legal part are runs of the triple. -/
theorem trun_mono (hL : PrefixClosed Lg) {x y : TSt E S A} {p : List (Move E (sig1 A B'))}
    (h : TRun (restrictLog Lg t).1 (satP (restrictLog Lg t)) x p y) : TRun t.1 (satP t) x p y := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (tstep_mono hL hs) ih

/-- A Proponent step of the legal part starts at a legal state. -/
theorem stLegal_of_tstep (hL : PrefixClosed Lg) {x y : TSt E S A} {o : Move E (sig1 A B')}
    (h : TStep (restrictLog Lg t).1 (satP (restrictLog Lg t)) x o y) (ho : o.IsP) :
    StLegal Lg x := by
  cases h with
  | ask => exact absurd ho (by simp [Move.IsP])
  | call s a c m hm => exact (satP_restrictLog hL s a ▸ hm).2
  | reply => exact absurd ho (by simp [Move.IsP])
  | ret s a c b s' hb => exact hb.2
  | trap s a c hb => exact hb.2
  | deadAsk => exact absurd ho (by simp [Move.IsP])

/-- A Proponent step of the triple from a legal state is a step of the legal part. -/
theorem tstep_restrict {x y : TSt E S A} {o : Move E (sig1 A B')}
    (h : TStep t.1 (satP t) x o y) (hx : o.IsP → StLegal Lg x) :
    TStep (restrictLog Lg t).1 (satP (restrictLog Lg t)) x o y := by
  cases h with
  | ask => exact .ask _ _
  | call s a c m hm => exact .call s a c m (.inl ⟨hm, hx trivial⟩)
  | reply => exact .reply _ _ _ _ _
  | ret s a c b s' hb => exact .ret s a c b s' ⟨hb, hx trivial⟩
  | trap s a c hb => exact .trap s a c ⟨hb, hx trivial⟩
  | deadAsk => exact .deadAsk _

/-- **A run whose states before Proponent moves are legal is a run of the legal part.** -/
theorem trun_restrict {x y : TSt E S A} {p : List (Move E (sig1 A B'))}
    (h : TRun t.1 (satP t) x p y)
    (hl : ∀ p₁ o p₂ z, p = p₁ ++ o :: p₂ → o.IsP → TRun t.1 (satP t) x p₁ z → StLegal Lg z) :
    TRun (restrictLog Lg t).1 (satP (restrictLog Lg t)) x p y := by
  induction h with
  | nil => exact .nil _
  | @cons x y' z o p hs hr ih =>
    refine .cons (tstep_restrict hs fun ho => hl [] o p x rfl ho (.nil _)) (ih ?_)
    intro p₁ o' p₂ z' hp ho' hz
    exact hl (o :: p₁) o' p₂ z' (by rw [hp]; rfl) ho' (.cons hs hz)

/-- In a run of the legal part, the state before a Proponent move is legal. -/
theorem stLegal_of_trun (hL : PrefixClosed Lg) {x y : TSt E S A} {p₁ p₂ : List (Move E (sig1 A B'))}
    {o : Move E (sig1 A B')} (h : TRun (restrictLog Lg t).1 (satP (restrictLog Lg t)) x (p₁ ++ o :: p₂) y)
    (ho : o.IsP) :
    ∃ z, TRun (restrictLog Lg t).1 (satP (restrictLog Lg t)) x p₁ z ∧ StLegal Lg z := by
  obtain ⟨z, hz, hr⟩ := h.of_append
  cases hr with
  | cons hs _ => exact ⟨z, hz, stLegal_of_tstep hL hs ho⟩

end Runs

/-! ## Plain traps and relabelling -/

section Relabel

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}

/-- A move that is not a plain trap. -/
def NotPlain : Move E (sig1 A (B ⊕ PUnit.{u + 1})) → Prop
  | .inr (.ans _ (.inr _)) => False
  | _ => True

theorem notPlain_of_trun (hn : NoPlainTrap t) {x y : TSt E S A}
    {p : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))} (h : TRun t.1 (satP t) x p y) :
    ∀ o ∈ p, NotPlain o := by
  induction h with
  | nil => simp
  | cons hs _ ih =>
    intro o ho
    rcases List.mem_cons.1 ho with rfl | ho
    · cases hs with
      | trap s a c hb => exact (hn s a c hb).elim
      | _ => trivial
    · exact ih o ho

theorem relMove_inj {o o' : Move E (sig1 A (B ⊕ PUnit.{u + 1}))} (h : NotPlain o)
    (h' : NotPlain o') (he : relMove o = relMove o') : o = o' := by
  rcases o with (_ | _) | (_ | ⟨_, (_ | _) | _⟩) <;>
    rcases o' with (_ | _) | (_ | ⟨_, (_ | _) | _⟩) <;>
    simp_all [relMove, merge, NotPlain]

theorem map_relMove_inj {p p' : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))}
    (h : ∀ o ∈ p, NotPlain o) (h' : ∀ o ∈ p', NotPlain o)
    (he : p.map relMove = p'.map relMove) : p = p' := by
  induction p generalizing p' with
  | nil => cases p' <;> simp_all
  | cons o p ih =>
    cases p' with
    | nil => simp at he
    | cons o' p' =>
      simp only [List.map_cons, List.cons.injEq] at he
      simp only [List.mem_cons, forall_eq_or_imp] at h h'
      rw [relMove_inj h.1 h'.1 he.1, ih h.2 h'.2 he.2]

theorem relMove_isP {o : Move E (sig1 A (B ⊕ PUnit.{u + 1}))} : (relMove o).IsP ↔ o.IsP := by
  rcases o with (_ | _) | (_ | _) <;> simp [relMove, Move.IsP]

/-- Splitting a relabelled play. -/
theorem map_eq_split {p : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))}
    {q₁ q₂ : List (Move E (sig1 A B))} {o : Move E (sig1 A B)}
    (h : p.map relMove = q₁ ++ o :: q₂) :
    ∃ p₁ o' p₂, p = p₁ ++ o' :: p₂ ∧ p₁.map relMove = q₁ ∧ relMove o' = o ∧
      p₂.map relMove = q₂ := by
  obtain ⟨p₁, r, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 h
  obtain ⟨o', p₂, rfl, h₃, h₄⟩ := List.map_eq_cons_iff.1 h₂
  exact ⟨p₁, o', p₂, rfl, h₁, h₃, h₄⟩

end Relabel

/-! ## Finite plays -/

section Plays

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {s₀ : S}

/-- From a legal-part run along `p`, the relabelled play is Proponent-legal. -/
theorem pLegal_of_trun (hd : StoreDet t) (hn : NoPlainTrap t) (hL : PrefixClosed Lg)
    {p : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))} {y : TSt E S A}
    (h : TRun (restrictLog Lg t).1 (satP (restrictLog Lg t)) (.idle s₀) p y) :
    PLegal Lg t s₀ (p.map relMove) := by
  intro q₁ o q₂ hq ho p₁ z hp₁ hz
  obtain ⟨p₁', o', p₂', rfl, h₁, h₂, -⟩ := map_eq_split hq
  obtain ⟨z', hz', hl⟩ := stLegal_of_trun hL h (relMove_isP.1 (h₂ ▸ ho))
  have hm := trun_mono hL hz'
  have hpp : p₁ = p₁' :=
    map_relMove_inj (notPlain_of_trun hn hz) (notPlain_of_trun hn hm) (hp₁.trans h₁.symm)
  subst hpp
  rw [TRun.det_of_storeDet hd hz hm]
  exact hl

/-- From a run along `p` whose relabelling is Proponent-legal, a run of the legal part. -/
theorem trun_of_pLegal {p : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))} {y : TSt E S A}
    (h : TRun t.1 (satP t) (.idle s₀) p y) (hl : PLegal Lg t s₀ (p.map relMove)) :
    TRun (restrictLog Lg t).1 (satP (restrictLog Lg t)) (.idle s₀) p y := by
  refine trun_restrict h fun p₁ o p₂ z hp ho hz => ?_
  subst hp
  exact hl (p₁.map relMove) (relMove o) (p₂.map relMove) (by simp) (relMove_isP.2 ho) p₁ z rfl hz

theorem mem_threadS_restrictLog (hd : StoreDet t) (hn : NoPlainTrap t) (hL : PrefixClosed Lg)
    {q : List (Move E (sig1 A B))} :
    q ∈ (threadS (restrictLog Lg t) s₀).toStrategy ↔
      q ∈ (threadS t s₀).toStrategy ∧ PLegal Lg t s₀ q := by
  constructor
  · rintro ⟨p, ⟨y, hy⟩, rfl⟩
    exact ⟨⟨p, ⟨y, trun_mono hL hy⟩, rfl⟩, pLegal_of_trun hd hn hL hy⟩
  · rintro ⟨⟨p, ⟨y, hy⟩, rfl⟩, hl⟩
    exact ⟨p, ⟨y, trun_of_pLegal hy hl⟩, rfl⟩

/-- Without hypotheses, the legal part's session plays are plays of the session. -/
theorem threadS_restrictLog_le (hL : PrefixClosed Lg) :
    threadS (restrictLog Lg t) s₀ ≤ threadS t s₀ := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨p, ⟨y, hy⟩, rfl⟩
    exact ⟨p, ⟨y, trun_mono hL hy⟩, rfl⟩
  · rintro _ ⟨p, ⟨s, a, c, hy, hc⟩, rfl⟩
    exact ⟨p, ⟨s, a, c, trun_mono hL hy, hc.1⟩, rfl⟩
  · rintro _ ⟨I, ⟨hI, hsub, hk⟩, rfl⟩
    refine ⟨I, ⟨hI, fun p hp => ?_, ?_⟩, rfl⟩
    · obtain ⟨y, hy⟩ := hsub hp
      exact ⟨y, trun_mono hL hy⟩
    · rcases hk with ⟨pre, s, a, ω, hpre, hω, rfl⟩ | hk
      · exact .inl ⟨pre, s, a, ω, trun_mono hL hpre, hω.1, rfl⟩
      · refine .inr fun p hp => ?_
        obtain ⟨p', hp', hpp, s, hs⟩ := hk p hp
        exact ⟨p', hp', hpp, s, trun_mono hL hs⟩

end Plays

/-! ## Divergence -/

section Div

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {s₀ : S}

theorem div_threadS_restrictLog (hd : StoreDet t) (hn : NoPlainTrap t) (hL : PrefixClosed Lg)
    {q : List (Move E (sig1 A B))} :
    q ∈ (threadS (restrictLog Lg t) s₀).div ↔ q ∈ (threadS t s₀).div ∧ SLegal Lg t s₀ q := by
  constructor
  · rintro ⟨p, ⟨s, a, c, hy, hc⟩, rfl⟩
    have hm := trun_mono hL hy
    refine ⟨⟨p, ⟨s, a, c, hm, hc.1⟩, rfl⟩, pLegal_of_trun hd hn hL hy, ?_⟩
    intro p' z hp' hz
    have hpp : p' = p :=
      map_relMove_inj (notPlain_of_trun hn hz) (notPlain_of_trun hn hm) hp'
    subst hpp
    rw [TRun.det_of_storeDet hd hz hm]
    exact hc.2
  · rintro ⟨⟨p, ⟨s, a, c, hy, hc⟩, rfl⟩, hl, he⟩
    exact ⟨p, ⟨s, a, c, trun_of_pLegal hy hl, hc, he p _ rfl hy⟩, rfl⟩

end Div

/-! ## Infinite plays -/

section Inf

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {s₀ : S}

theorem streamTake_succ {α : Type u} (ω : ℕ → α) (k : ℕ) :
    streamTake ω (k + 1) = streamTake ω k ++ [ω k] := by
  simp only [streamTake]; rw [List.ofFn_succ_last]; rfl

theorem callMoves_append {F : Sig.{u}} (c d : List (Call E)) :
    (callMoves (c ++ d) : List (Move E F)) = callMoves c ++ callMoves d := by
  simp [callMoves]

/-- The calls of a productive stream are a run of the threading automaton. -/
theorem trun_stream {s : S} {a : A} {ω : ℕ → Call E} (hω : ω ∈ t.2.2 s a) (k : ℕ) :
    TRun t.1 (satP t) (.run s a []) (callMoves (streamTake ω k)) (.run s a (streamTake ω k)) := by
  induction k with
  | zero => simpa [streamTake, callMoves] using TRun.nil (f := t.1) (P := satP t) (.run s a [])
  | succ k ih =>
    rw [streamTake_succ, callMoves_append]
    refine ih.append (.cons (.call s a _ (ω k).1 (.inr (.inr (.inr ⟨ω, hω, k, rfl, rfl⟩))))
      (.cons (.reply s a _ (ω k).1 (ω k).2) (.nil _)))

theorem mem_streamPlay_self (pre : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))) (a : A)
    (ω : ℕ → Call E) (k : ℕ) :
    pre ++ .inr (.ask a) :: (callMoves (streamTake ω k) ++ [.inl (.ask (ω k).1)]) ∈
      StratThread.streamPlay pre a ω := by
  refine ⟨k + 1, ?_⟩
  rw [streamTake_succ, callMoves_append]
  exact ⟨[.inl (.ans (ω k).1 (ω k).2)], by simp [callMoves]⟩

theorem inf_threadS_restrictLog (hd : StoreDet t) (hn : NoPlainTrap t) (hL : PrefixClosed Lg)
    {J : Set (List (Move E (sig1 A B)))} :
    J ∈ (threadS (restrictLog Lg t) s₀).inf ↔
      J ∈ (threadS t s₀).inf ∧ ∀ q ∈ J, PLegal Lg t s₀ q := by
  constructor
  · rintro ⟨I, hI, rfl⟩
    refine ⟨(threadS_restrictLog_le hL).2.2 ⟨I, hI, rfl⟩, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨y, hy⟩ := hI.2.1 hp
    exact pLegal_of_trun hd hn hL hy
  · rintro ⟨⟨I, ⟨hI, hsub, hk⟩, rfl⟩, hl⟩
    have hrun : ∀ {p y}, p ∈ I → TRun t.1 (satP t) (.idle s₀) p y →
        TRun (restrictLog Lg t).1 (satP (restrictLog Lg t)) (.idle s₀) p y :=
      fun hp hy => trun_of_pLegal hy (hl _ ⟨_, hp, rfl⟩)
    refine ⟨I, ⟨hI, fun p hp => ?_, ?_⟩, rfl⟩
    · obtain ⟨y, hy⟩ := hsub hp
      exact ⟨y, hrun hp hy⟩
    · rcases hk with ⟨pre, s, a, ω, hpre, hω, rfl⟩ | hk
      · refine .inl ⟨pre, s, a, ω, hrun ⟨0, [.inr (.ask a)], by simp [streamTake, callMoves]⟩ hpre,
          ⟨hω, fun k => ?_⟩, rfl⟩
        have hmem := mem_streamPlay_self pre a ω k
        have hr : TRun t.1 (satP t) (.idle s₀) (pre ++ .inr (.ask a) :: callMoves (streamTake ω k))
            (.run s a (streamTake ω k)) :=
          hpre.append (.cons (.ask s a) (trun_stream hω k))
        refine hl _ ⟨_, hmem, rfl⟩ (List.map relMove (pre ++ .inr (.ask a) ::
          callMoves (streamTake ω k))) (.inl (.ask (ω k).1)) [] ?_ (by simp [Move.IsP]) _ _ rfl hr
        simp [relMove]
      · refine .inr fun p hp => ?_
        obtain ⟨p', hp', hpp, s, hs⟩ := hk p hp
        exact ⟨p', hp', hpp, s, hrun hp' hs⟩

end Inf

/-! ## Plays ending in a Proponent move -/

section Snoc

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {s₀ : S}

/-- **A play ending in a Proponent move is Proponent-legal iff the play before it is legal, its
end included.** -/
theorem pLegal_snoc {q : List (Move E (sig1 A B))} {o : Move E (sig1 A B)} (ho : o.IsP) :
    PLegal Lg t s₀ (q ++ [o]) ↔ SLegal Lg t s₀ q := by
  constructor
  · intro h
    refine ⟨fun q₁ o' q₂ hq ho' => h q₁ o' (q₂ ++ [o]) (by rw [hq]; simp) ho', ?_⟩
    exact h q o [] rfl ho
  · rintro ⟨h, he⟩ q₁ o' q₂ hq ho'
    rcases q₂.eq_nil_or_concat with rfl | ⟨q₂', o'', rfl⟩
    · obtain ⟨rfl, -⟩ := List.append_inj' hq rfl
      exact he
    · have hq' : q ++ [o] = (q₁ ++ o' :: q₂') ++ [o''] := by rw [hq]; simp
      obtain ⟨hq'', -⟩ := List.append_inj' hq' rfl
      exact h q₁ o' q₂' hq'' ho'

end Snoc

end Silmaril.Proofs.Games.Abstract.SessionLegal
