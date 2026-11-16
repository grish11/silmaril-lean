module

public import Silmaril.Games.Abstract.SessionLink.Defs
public import Silmaril.Games.Abstract.StratSession.Thms
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction

/-!
# Linking sessions: the session automaton (proofs)

`threadS t s₀` relabels the threading automaton of `StratThread` along `StratSession.merge`. Here
the relabelled automaton is given directly (`SStep`, `SRun`) on the moves of `sig1 A B`: a return
`.ret x s'` answers `x`, a plain trap answers `.inr ()` and kills the session.

* `srun_iff`: runs of the session automaton are the relabelled runs of the threading automaton;
  hence the plays (`mem_plays`) and divergences (`mem_div`) of `threadS t s₀`;
* `lift`: a run ending live is the relabelling of a threading run along `unrel`; hence the
  infinite plays completing infinitely many rounds (`mem_inf_of_rounds`) and stream plays
  (`mem_inf_of_stream`) of `threadS t s₀`;
* `shape`: the shape of a play by its final state (completed rounds, then a partial round);
* lists of moves: call moves, session rounds, and the moves of served calls.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLink

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-! ## Lists of moves -/

section Moves

variable {F : Sig.{u}}

@[simp] theorem callMoves_nil : (callMoves ([] : List (Call E)) : List (Move E F)) = [] := rfl

@[simp] theorem callMoves_cons (x : Call E) (c : List (Call E)) :
    (callMoves (x :: c) : List (Move E F)) =
      .inl (.ask x.1) :: .inl (.ans x.1 x.2) :: callMoves c :=
  rfl

@[simp] theorem callMoves_append (c d : List (Call E)) :
    (callMoves (c ++ d) : List (Move E F)) = callMoves c ++ callMoves d := by
  simp [callMoves]

theorem length_callMoves (c : List (Call E)) :
    (callMoves c : List (Move E F)).length = 2 * c.length := by
  induction c with
  | nil => rfl
  | cons x c ih => simp [ih]; omega

theorem streamTake_succ {α : Type u} (ω : ℕ → α) (k : ℕ) :
    streamTake ω (k + 1) = streamTake ω k ++ [ω k] := by
  simp only [streamTake]; rw [List.ofFn_succ_last]; rfl

@[simp] theorem streamTake_zero {α : Type u} (ω : ℕ → α) : streamTake ω 0 = [] := rfl

@[simp] theorem length_streamTake {α : Type u} (ω : ℕ → α) (k : ℕ) :
    (streamTake ω k).length = k := by
  simp [streamTake]

theorem streamTake_prefix {α : Type u} (ω : ℕ → α) {j k : ℕ} (h : j ≤ k) :
    streamTake ω j <+: streamTake ω k := by
  induction k with
  | zero => cases Nat.le_zero.1 h; exact List.prefix_refl _
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h' | h'
    · rw [streamTake_succ]; exact (ih (by omega)).trans (List.prefix_append _ _)
    · cases le_antisymm h h'; exact List.prefix_refl _

/-- A prefix of a stream is followed by the next element. -/
theorem streamTake_split {α : Type u} (ω : ℕ → α) {j k : ℕ} (h : j < k) :
    ∃ r, streamTake ω k = streamTake ω j ++ ω j :: r := by
  obtain ⟨r, hr⟩ := streamTake_prefix ω (Nat.succ_le_of_lt h)
  exact ⟨r, by rw [← hr, streamTake_succ]; simp⟩

theorem callPre_append {c d₁ d₂ : List (Call E)} {m : E.Op} (h : CallPre c m (d₁ ++ d₂)) :
    CallPre c m d₁ ∨ ∃ c', c = d₁ ++ c' ∧ CallPre c' m d₂ := by
  obtain ⟨n, r, hr⟩ := h
  rcases List.append_eq_append_iff.1 hr with ⟨a', h₁, h₂⟩ | ⟨c', h₁, h₂⟩
  · -- `d₁ ++ a' = c`
    exact .inr ⟨a', h₁, by
      rcases a' with _ | ⟨y, a'⟩
      · simp at h₁ h₂; exact ⟨n, r, by simp [h₂]⟩
      · simp at h₂; exact ⟨n, r, by rw [List.append_cons]; simp [h₂]⟩⟩
  · rcases c' with _ | ⟨y, c'⟩
    · simp at h₁ h₂; exact .inr ⟨[], by simp [h₁], n, r, by simp [h₂]⟩
    · simp at h₂
      obtain ⟨rfl, rfl⟩ := h₂
      exact .inl ⟨n, c', h₁⟩

theorem callPre_append_left {c d₁ d₂ : List (Call E)} {m : E.Op} (h : CallPre c m d₁) :
    CallPre c m (d₁ ++ d₂) := by
  obtain ⟨n, r, rfl⟩ := h
  exact ⟨n, r ++ d₂, by simp⟩

theorem callPre_append_right {c d₁ d₂ : List (Call E)} {m : E.Op} (h : CallPre c m d₂) :
    CallPre (d₁ ++ c) m (d₁ ++ d₂) := by
  obtain ⟨n, r, rfl⟩ := h
  exact ⟨n, r, by simp⟩

end Moves

/-! ## Session rounds -/

section Rounds

variable {B' : Type u}

@[simp] theorem sroundsMoves_nil :
    (sroundsMoves ([] : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
      List (Move E (sig1 A B))) = [] := rfl

@[simp] theorem sroundsMoves_cons (r : A × List (Call E) × (B ⊕ PUnit.{u + 1}))
    (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
    (sroundsMoves (r :: rs) : List (Move E (sig1 A B))) = sroundMoves r ++ sroundsMoves rs := rfl

@[simp] theorem sroundsMoves_append (rs rs' : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
    (sroundsMoves (rs ++ rs') : List (Move E (sig1 A B))) =
      sroundsMoves rs ++ sroundsMoves rs' := by
  simp [sroundsMoves]

@[simp] theorem served_nil :
    SessionLink.served ([] : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) = [] := rfl

@[simp] theorem served_append (rs rs' : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
    SessionLink.served (rs ++ rs') = SessionLink.served rs ++ SessionLink.served rs' := by
  simp [SessionLink.served]

@[simp] theorem served_cons (r : A × List (Call E) × (B ⊕ PUnit.{u + 1}))
    (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
    SessionLink.served (r :: rs) = ⟨r.1, r.2.2⟩ :: SessionLink.served rs := rfl

@[simp] theorem servedLog_nil :
    SessionLink.servedLog ([] : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) = [] := rfl

@[simp] theorem servedLog_cons (r : A × List (Call E) × (B ⊕ PUnit.{u + 1}))
    (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
    SessionLink.servedLog (r :: rs) = r.2.1 ++ SessionLink.servedLog rs := rfl

@[simp] theorem servedLog_append (rs rs' : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
    SessionLink.servedLog (rs ++ rs') =
      SessionLink.servedLog rs ++ SessionLink.servedLog rs' := by
  simp [SessionLink.servedLog]

variable {t : ObsTriple E S A B'}

theorem rounds_snoc {s s₁ s₂ : S} {rs : List (A × List (Call E) × B')} {a : A}
    {c : List (Call E)} {b : B'} (h : Rounds t s rs s₁) (hr : (c, .ret b s₂) ∈ t.1 s₁ a) :
    Rounds t s (rs ++ [(a, c, b)]) s₂ := by
  induction h with
  | nil => exact .cons hr (.nil _)
  | cons h _ ih => exact .cons h (ih hr)

theorem rounds_append {s s₁ s₂ : S} {rs rs' : List (A × List (Call E) × B')}
    (h : Rounds t s rs s₁) (h' : Rounds t s₁ rs' s₂) : Rounds t s (rs ++ rs') s₂ := by
  induction h with
  | nil => exact h'
  | cons h _ ih => exact .cons h (ih h')

theorem rounds_of_append {s s₂ : S} {rs rs' : List (A × List (Call E) × B')}
    (h : Rounds t s (rs ++ rs') s₂) : ∃ s₁, Rounds t s rs s₁ ∧ Rounds t s₁ rs' s₂ := by
  induction rs generalizing s with
  | nil => exact ⟨s, .nil _, h⟩
  | cons r rs ih =>
    cases h with
    | cons hr h =>
      obtain ⟨s₁, h₁, h₂⟩ := ih h
      exact ⟨s₁, .cons hr h₁, h₂⟩

theorem rounds_det (ht : StoreDet t) {s s₁ s₂ : S} {rs : List (A × List (Call E) × B')}
    (h₁ : Rounds t s rs s₁) (h₂ : Rounds t s rs s₂) : s₁ = s₂ := by
  induction h₁ with
  | nil => cases h₂; rfl
  | cons hr _ ih =>
    cases h₂ with
    | cons hr' h₂ => exact ih (ht _ _ _ _ _ _ hr hr' ▸ h₂)

end Rounds

/-! ## The session automaton -/

variable {B' : Type u}

/-- One move of the session automaton of a store-retaining triple `t`. -/
inductive SStep (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) :
    TSt E S A → Move E (sig1 A B) → TSt E S A → Prop
  | ask (s : S) (a : A) : SStep t (.idle s) (.inr (.ask a)) (.run s a [])
  | call (s : S) (a : A) (c : List (Call E)) (m : E.Op) :
      (c, m) ∈ satP t s a → SStep t (.run s a c) (.inl (.ask m)) (.wait s a c m)
  | reply (s : S) (a : A) (c : List (Call E)) (m : E.Op) (n : E.Ar m) :
      SStep t (.wait s a c m) (.inl (.ans m n)) (.run s a (c ++ [⟨m, n⟩]))
  | ret (s : S) (a : A) (c : List (Call E)) (x : B ⊕ PUnit.{u + 1}) (s' : S) :
      (c, .ret x s') ∈ t.1 s a → SStep t (.run s a c) (.inr (.ans a x)) (.idle s')
  | trap (s : S) (a : A) (c : List (Call E)) :
      (c, .trap) ∈ t.1 s a → SStep t (.run s a c) (.inr (.ans a (.inr PUnit.unit))) .dead
  | deadAsk (a : A) : SStep t .dead (.inr (.ask a)) (.stuck a)

/-- Runs of the session automaton. -/
inductive SRun (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) :
    TSt E S A → List (Move E (sig1 A B)) → TSt E S A → Prop
  | nil (x : TSt E S A) : SRun t x [] x
  | cons {x y z : TSt E S A} {o : Move E (sig1 A B)} {q : List (Move E (sig1 A B))} :
      SStep t x o y → SRun t y q z → SRun t x (o :: q) z

section SRun

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}

theorem SRun.single {x y : TSt E S A} {o : Move E (sig1 A B)} (h : SStep t x o y) :
    SRun t x [o] y :=
  .cons h (.nil _)

theorem SRun.append {x y z : TSt E S A} {q q' : List (Move E (sig1 A B))}
    (h₁ : SRun t x q y) (h₂ : SRun t y q' z) : SRun t x (q ++ q') z := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h (ih h₂)

theorem SRun.of_append {x z : TSt E S A} {q q' : List (Move E (sig1 A B))}
    (h : SRun t x (q ++ q') z) : ∃ y, SRun t x q y ∧ SRun t y q' z := by
  induction q generalizing x with
  | nil => exact ⟨x, .nil x, h⟩
  | cons o q ih =>
    cases h with
    | cons h hr => obtain ⟨y, h₁, h₂⟩ := ih hr; exact ⟨y, .cons h h₁, h₂⟩

theorem SRun.nil_eq {x y : TSt E S A} (h : SRun t x [] y) : x = y := by
  cases h; rfl

theorem SRun.snoc_iff {x z : TSt E S A} {q : List (Move E (sig1 A B))} {o : Move E (sig1 A B)} :
    SRun t x (q ++ [o]) z ↔ ∃ y, SRun t x q y ∧ SStep t y o z := by
  constructor
  · intro h
    obtain ⟨y, h₁, h₂⟩ := h.of_append
    cases h₂ with
    | cons h hn => cases hn; exact ⟨y, h₁, h⟩
  · rintro ⟨y, h₁, h₂⟩
    exact h₁.append (.single h₂)

/-- Relabelling a threading step gives a session step. -/
theorem sstep_of_tstep {x y : TSt E S A} {o : Move E (sig1 A (B ⊕ PUnit.{u + 1}))}
    (h : TStep t.1 (satP t) x o y) : SStep t x (relMove o) y := by
  cases h with
  | ask => exact .ask _ _
  | call _ _ _ _ h => exact .call _ _ _ _ h
  | reply => exact .reply _ _ _ _ _
  | ret _ _ _ _ _ h => exact .ret _ _ _ _ _ h
  | trap _ _ _ h => exact .trap _ _ _ h
  | deadAsk => exact .deadAsk _

/-- **Session runs are relabelled threading runs.** -/
theorem srun_iff {x y : TSt E S A} {q : List (Move E (sig1 A B))} :
    SRun t x q y ↔ ∃ p, TRun t.1 (satP t) x p y ∧ p.map relMove = q := by
  constructor
  · intro h
    induction h with
    | nil x => exact ⟨[], .nil x, rfl⟩
    | cons hst _ ih =>
      obtain ⟨p, hp, rfl⟩ := ih
      cases hst with
      | ask s a => exact ⟨_, .cons (.ask s a) hp, rfl⟩
      | call s a c m h => exact ⟨_, .cons (.call s a c m h) hp, rfl⟩
      | reply s a c m n => exact ⟨_, .cons (.reply s a c m n) hp, rfl⟩
      | ret s a c x s' h => exact ⟨_, .cons (.ret s a c x s' h) hp, rfl⟩
      | trap s a c h => exact ⟨_, .cons (.trap s a c h) hp, rfl⟩
      | deadAsk a => exact ⟨_, .cons (.deadAsk a) hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    induction hp with
    | nil x => exact .nil x
    | cons h _ ih => exact .cons (sstep_of_tstep h) ih

/-- The plays of a session are the runs of the session automaton. -/
theorem mem_plays {s₀ : S} {q : List (Move E (sig1 A B))} :
    q ∈ (threadS t s₀).toStrategy ↔ ∃ y, SRun t (.idle s₀) q y := by
  constructor
  · rintro ⟨p, ⟨y, hp⟩, rfl⟩
    exact ⟨y, srun_iff.2 ⟨p, hp, rfl⟩⟩
  · rintro ⟨y, h⟩
    obtain ⟨p, hp, rfl⟩ := srun_iff.1 h
    exact ⟨p, ⟨y, hp⟩, rfl⟩

/-- The divergences of a session are the runs to a divergent behaviour. -/
theorem mem_div {s₀ : S} {q : List (Move E (sig1 A B))} :
    q ∈ (threadS t s₀).div ↔
      ∃ s a c, SRun t (.idle s₀) q (.run s a c) ∧ (c, .div) ∈ t.1 s a := by
  constructor
  · rintro ⟨p, ⟨s, a, c, hp, hd⟩, rfl⟩
    exact ⟨s, a, c, srun_iff.2 ⟨p, hp, rfl⟩, hd⟩
  · rintro ⟨s, a, c, h, hd⟩
    obtain ⟨p, hp, rfl⟩ := srun_iff.1 h
    exact ⟨p, ⟨s, a, c, hp, hd⟩, rfl⟩

/-! ## Lifting live runs -/

/-- The inverse of `relMove` on moves of live runs: an answer is a return. -/
def unrel : Move E (sig1 A B) → Move E (sig1 A (B ⊕ PUnit.{u + 1}))
  | .inl e => .inl e
  | .inr (.ask a) => .inr (.ask a)
  | .inr (.ans a x) => .inr (.ans a (.inl x))

@[simp] theorem relMove_unrel (o : Move E (sig1 A B)) : relMove (unrel o) = o := by
  rcases o with e | (a | ⟨a, x⟩) <;> rfl

@[simp] theorem relMove_comp_unrel : (relMove ∘ unrel : Move E (sig1 A B) → _) = id :=
  funext relMove_unrel

theorem map_relMove_unrel (q : List (Move E (sig1 A B))) :
    (q.map unrel).map relMove = q := by
  simp [List.map_map, Function.comp_def]

/-- A live state: not after a plain trap. -/
def Live : TSt E S A → Prop
  | .dead => False
  | .stuck _ => False
  | _ => True

theorem SRun.dead_not_live {y : TSt E S A} {q : List (Move E (sig1 A B))}
    (h : SRun t .dead q y) : ¬ Live y := by
  generalize hx : (TSt.dead : TSt E S A) = x at h
  induction h with
  | nil => subst hx; exact id
  | cons hst hr ih =>
    subst hx
    cases hst
    clear ih
    cases hr with
    | nil => exact id
    | cons h _ => cases h

/-- **A run ending live is a relabelled threading run along `unrel`.** -/
theorem lift {x y : TSt E S A} {q : List (Move E (sig1 A B))} (h : SRun t x q y) (hy : Live y) :
    TRun t.1 (satP t) x (q.map unrel) y := by
  induction h with
  | nil x => exact .nil x
  | cons hst hr ih =>
    have ih := ih hy
    cases hst with
    | ask s a => exact .cons (.ask s a) ih
    | call s a c m h => exact .cons (.call s a c m h) ih
    | reply s a c m n => exact .cons (.reply s a c m n) ih
    | ret s a c x s' h => exact .cons (.ret s a c x s' h) ih
    | trap => exact absurd hy (hr.dead_not_live)
    | deadAsk => exact absurd hy (SRun.dead_not_live (.cons (.deadAsk _) hr))

theorem isInfPlay_map {α β : Type u} (f : α → β) {I : Set (List α)} (hI : IsInfPlay I) :
    IsInfPlay (List.map f '' I) where
  of_prefix := by
    rintro s _ ⟨q, hq, rfl⟩ hs
    refine ⟨q.take s.length, hI.of_prefix hq (List.take_prefix _ _), ?_⟩
    rw [List.map_take]
    exact (List.prefix_iff_eq_take.1 hs).symm
  total := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨q, hq, rfl⟩
    rcases hI.total hs hq with h | h
    · exact .inl (h.map _)
    · exact .inr (h.map _)
  unbounded k := by
    obtain ⟨s, hs, hk⟩ := hI.unbounded k
    exact ⟨_, ⟨s, hs, rfl⟩, by simpa using hk⟩

theorem image_unrel (I : Set (List (Move E (sig1 A B)))) :
    List.map relMove '' (List.map (unrel (B := B)) '' I) = I := by
  ext q
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rwa [map_relMove_unrel]
  · intro hq
    exact ⟨_, ⟨q, hq, rfl⟩, map_relMove_unrel q⟩

/-- **Infinite plays completing infinitely many rounds.** -/
theorem mem_inf_of_rounds {s₀ : S} {I : Set (List (Move E (sig1 A B)))} (hI : IsInfPlay I)
    (hB : ∀ p ∈ I, ∃ p' ∈ I, p <+: p' ∧ ∃ s, SRun t (.idle s₀) p' (.idle s)) :
    I ∈ (threadS t s₀).inf := by
  refine ⟨List.map unrel '' I, ⟨isInfPlay_map _ hI, ?_, .inr ?_⟩, (image_unrel I).symm⟩
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨p', -, hpp, s, hs⟩ := hB p hp
    have h := lift hs trivial
    obtain ⟨r, rfl⟩ := hpp
    rw [List.map_append] at h
    obtain ⟨y, h₁, -⟩ := h.of_append
    exact ⟨y, h₁⟩
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨p', hp', hpp, s, hs⟩ := hB p hp
    exact ⟨_, ⟨p', hp', rfl⟩, hpp.map _, s, lift hs trivial⟩

/-- The relabelled stream play is the stream play of the relabelled prefix. -/
theorem image_streamPlay (pre : List (Move E (sig1 A B))) (a : A) (ω : ℕ → Call E) :
    List.map relMove '' streamPlay (pre.map unrel) a ω = streamPlay pre a ω := by
  have hc : ∀ k, ((callMoves (streamTake ω k) : List (Move E (sig1 A (B ⊕ PUnit.{u + 1}))))).map
      relMove = callMoves (streamTake ω k) := fun k => by
    induction (streamTake ω k) with
    | nil => rfl
    | cons x c ih => simp [ih, relMove]
  ext q
  constructor
  · rintro ⟨p, ⟨k, hk⟩, rfl⟩
    refine ⟨k, ?_⟩
    have := hk.map relMove
    simpa [List.map_append, map_relMove_unrel, hc, relMove] using this
  · rintro ⟨k, hk⟩
    have hq : q.map unrel <+: (pre.map unrel) ++ .inr (.ask a) ::
        callMoves (streamTake ω k) := by
      have := hk.map unrel
      have hc' : (callMoves (streamTake ω k) : List (Move E (sig1 A B))).map unrel =
          callMoves (streamTake ω k) := by
        induction (streamTake ω k) with
        | nil => rfl
        | cons x c ih => simp [ih, unrel]
      simpa [hc', unrel] using this
    exact ⟨_, ⟨k, hq⟩, map_relMove_unrel q⟩

/-- **A stream after a run to an idle store is an infinite play.** -/
theorem mem_inf_of_stream {s₀ s : S} {pre : List (Move E (sig1 A B))} {a : A} {ω : ℕ → Call E}
    (hpre : SRun t (.idle s₀) pre (.idle s)) (hω : ω ∈ t.2.2 s a) :
    streamPlay pre a ω ∈ (threadS t s₀).inf :=
  ⟨_, StratThread.streamPlay_mem (lift hpre trivial) hω, (image_streamPlay pre a ω).symm⟩

/-! ## Building runs -/

theorem run_callMoves {s : S} {a : A} (d : List (Call E)) {c₀ : List (Call E)}
    (hd : ∀ c m, CallPre c m (c₀ ++ d) → (c, m) ∈ satP t s a) :
    SRun t (.run s a c₀) (callMoves d) (.run s a (c₀ ++ d)) := by
  induction d generalizing c₀ with
  | nil => simpa using SRun.nil _
  | cons x d ih =>
    have h := ih (c₀ := c₀ ++ [x]) (by simpa using hd)
    simp only [List.append_assoc, List.singleton_append] at h
    exact .cons (.call s a c₀ x.1 (hd c₀ x.1 ⟨x.2, d, rfl⟩)) (.cons (.reply s a c₀ x.1 x.2) h)

/-- The call prefixes forced by a behaviour. -/
theorem satP_of_beh {s : S} {a : A} {d : List (Call E)} {e : End S (B ⊕ PUnit.{u + 1})}
    (h : (d, e) ∈ t.1 s a) {c : List (Call E)} {m : E.Op} (hc : CallPre c m d) :
    (c, m) ∈ satP t s a :=
  .inr (.inr (.inl ⟨d, e, h, hc⟩))

/-- A round of the session automaton. -/
theorem run_round {s s' : S} {a : A} {c : List (Call E)} {x : B ⊕ PUnit.{u + 1}}
    (h : (c, .ret x s') ∈ t.1 s a) : SRun t (.idle s) (sroundMoves (a, c, x)) (.idle s') := by
  have hr := run_callMoves (t := t) (s := s) (a := a) c (c₀ := [])
    fun _ _ hc => satP_of_beh h (by simpa using hc)
  simp only [List.nil_append] at hr
  exact .cons (.ask s a) (hr.append (.single (.ret s a c x s' h)))

/-- **Completed rounds are runs between idle states.** -/
theorem run_rounds {s s' : S} {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    (h : Rounds t s rs s') : SRun t (.idle s) (sroundsMoves rs) (.idle s') := by
  induction h with
  | nil => exact .nil _
  | cons hr _ ih => exact (run_round hr).append ih

/-! ## The shape of a run -/

/-- The shape of a play from `idle s` by its final state. -/
def Shape (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) (s : S) (q : List (Move E (sig1 A B))) :
    TSt E S A → Prop
  | .idle s₁ => ∃ rs, Rounds t s rs s₁ ∧ q = sroundsMoves rs
  | .run s₁ a c => ∃ rs, Rounds t s rs s₁ ∧ q = sroundsMoves rs ++ .inr (.ask a) :: callMoves c ∧
      (c = [] ∨ ∃ c₀ m n, c = c₀ ++ [⟨m, n⟩] ∧ (c₀, m) ∈ satP t s₁ a)
  | .wait s₁ a c m => ∃ rs, Rounds t s rs s₁ ∧
      q = sroundsMoves rs ++ .inr (.ask a) :: (callMoves c ++ [.inl (.ask m)]) ∧
      (c, m) ∈ satP t s₁ a
  | .dead => ∃ rs s₁ a c, Rounds t s rs s₁ ∧ (c, .trap) ∈ t.1 s₁ a ∧
      q = sroundsMoves rs ++ sroundMoves (a, c, .inr PUnit.unit)
  | .stuck a' => ∃ rs s₁ a c, Rounds t s rs s₁ ∧ (c, .trap) ∈ t.1 s₁ a ∧
      q = sroundsMoves rs ++ sroundMoves (a, c, .inr PUnit.unit) ++ [.inr (.ask a')]

/-- **The shape of a run from an idle state.** -/
theorem shape {s : S} {q : List (Move E (sig1 A B))} {y : TSt E S A}
    (h : SRun t (.idle s) q y) : Shape t s q y := by
  induction q using List.reverseRecOn generalizing y with
  | nil => cases h; exact ⟨[], .nil _, rfl⟩
  | append_singleton q o ih =>
    obtain ⟨x, hx, hst⟩ := SRun.snoc_iff.1 h
    have ih := ih hx
    cases hst with
    | ask s₁ a =>
      obtain ⟨rs, hrs, rfl⟩ := ih
      exact ⟨rs, hrs, by simp, .inl rfl⟩
    | call s₁ a c m hP =>
      obtain ⟨rs, hrs, rfl, -⟩ := ih
      exact ⟨rs, hrs, by simp, hP⟩
    | reply s₁ a c m n =>
      obtain ⟨rs, hrs, rfl, hP⟩ := ih
      exact ⟨rs, hrs, by simp, .inr ⟨c, m, n, rfl, hP⟩⟩
    | ret s₁ a c x s' hb =>
      obtain ⟨rs, hrs, rfl, -⟩ := ih
      exact ⟨rs ++ [(a, c, x)], rounds_snoc hrs hb, by simp [sroundMoves]⟩
    | trap s₁ a c hb =>
      obtain ⟨rs, hrs, rfl, -⟩ := ih
      exact ⟨rs, s₁, a, c, hrs, hb, by simp [sroundMoves]⟩
    | deadAsk a' =>
      obtain ⟨rs, s₁, a, c, hrs, hb, rfl⟩ := ih
      exact ⟨rs, s₁, a, c, hrs, hb, rfl⟩

end SRun

end Silmaril.Proofs.Games.Abstract.SessionLink
