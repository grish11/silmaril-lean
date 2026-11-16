module

public import Silmaril.Games.Abstract.StratThread.Defs
public import Silmaril.Games.Abstract.StratObs.Thms
public import Silmaril.Games.Div.Thms

/-!
# Threading a state-passing function: proofs

* List and stream facts (local copies of the small facts the play
  characterisations need).
* Reading rounds (`round_inv`, `rounds_inv`): from idle at `s` the automaton
  reads the moves of completed returning rounds exactly along `Rounds`.
* Membership characterisations: completed rounds, traps, pending calls,
  divergence and productive streams after completed rounds.
* Bisimulation soundness (`threadT_eq_of_isBisim`) by simulating runs.
* For store-deterministic triples, residuals after a round
  (`mem_after_round`, `div_after_round`, `extR_mem_inf`, `resR_mem_inf`) and the
  converse (`roundEq_of_eq`).
-/

public section

namespace Silmaril.Proofs.Games.Abstract.StratThread

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratThread
open Silmaril.Games.Abstract.StratObs (callMoves satP satP_prefix)

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-! ## Lists, calls and streams -/

section Lists

variable {α : Type u}

theorem prefix_append_iff {q r p : List α} :
    q <+: r ++ p ↔ q <+: r ∨ ∃ p', q = r ++ p' ∧ p' <+: p := by
  constructor
  · intro h
    rcases List.prefix_or_prefix_of_prefix h (List.prefix_append r p) with h' | ⟨p', rfl⟩
    · exact .inl h'
    · exact .inr ⟨p', rfl, (List.prefix_append_right_inj r).1 h⟩
  · rintro (h | ⟨p', rfl, h⟩)
    · exact List.prefix_append_of_prefix h
    · exact (List.prefix_append_right_inj r).2 h

end Lists

section Calls

variable {F : Sig.{u}}

@[simp] theorem callMoves_nil : (callMoves [] : List (Move E F)) = [] := rfl

@[simp] theorem callMoves_cons (x : Call E) (c : List (Call E)) :
    (callMoves (x :: c) : List (Move E F)) = .inl (.ask x.1) :: .inl (.ans x.1 x.2) :: callMoves c :=
  rfl

@[simp] theorem callMoves_append (c d : List (Call E)) :
    (callMoves (c ++ d) : List (Move E F)) = callMoves c ++ callMoves d := by
  simp [callMoves]

theorem length_callMoves (c : List (Call E)) :
    (callMoves c : List (Move E F)).length = 2 * c.length := by
  induction c with
  | nil => rfl
  | cons x c ih => simp [ih]; omega

theorem not_inr_mem_callMoves {c : List (Call E)} {y : Ev F} :
    (.inr y : Move E F) ∉ callMoves c := by
  induction c with
  | nil => simp
  | cons x c ih => simp [ih]

theorem prefix_of_callMoves {c d : List (Call E)}
    (h : (callMoves c : List (Move E F)) <+: callMoves d) : c <+: d := by
  induction c generalizing d with
  | nil => exact List.nil_prefix
  | cons x c ih =>
    cases d with
    | nil => simp at h
    | cons y d =>
      obtain ⟨m, n⟩ := x
      obtain ⟨m', n'⟩ := y
      simp only [callMoves_cons, List.cons_prefix_cons, Sum.inl.injEq, Ev.ask.injEq,
        Ev.ans.injEq] at h
      obtain ⟨rfl, ⟨-, hn⟩, h⟩ := h
      cases hn
      exact List.cons_prefix_cons.2 ⟨rfl, ih h⟩

end Calls

section Stream

variable {α : Type u}

@[simp] theorem length_streamTake (ω : ℕ → α) (k : ℕ) : (streamTake ω k).length = k := by
  simp [streamTake]

theorem getElem_streamTake (ω : ℕ → α) (k i : ℕ) (h : i < (streamTake ω k).length) :
    (streamTake ω k)[i] = ω i := by
  simp [streamTake]

theorem streamTake_succ (ω : ℕ → α) (k : ℕ) : streamTake ω (k + 1) = streamTake ω k ++ [ω k] := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  rw [getElem_streamTake]
  rcases Nat.lt_succ_iff_lt_or_eq.1 (by simpa using h₁) with h | rfl
  · rw [List.getElem_append_left (by simpa using h), getElem_streamTake]
  · simp

theorem streamTake_eq_append {ω : ℕ → α} {k : ℕ} {c₁ c₂ : List α} {x : α}
    (h : streamTake ω k = c₁ ++ x :: c₂) : streamTake ω c₁.length = c₁ ∧ ω c₁.length = x := by
  have hl : c₁.length < (streamTake ω k).length := by rw [h]; simp
  constructor
  · apply List.ext_getElem (by simp)
    intro i h₁ h₂
    have hi : i < (streamTake ω k).length := by simp at h₁; omega
    rw [getElem_streamTake, ← getElem_streamTake ω k i hi]
    simp only [h, List.getElem_append_left h₂]
  · rw [← getElem_streamTake ω k _ hl]
    simp [h]

theorem eq_of_streamTake_prefix {ω ω' : ℕ → α} {n k : ℕ}
    (h : streamTake ω n <+: streamTake ω' k) {j : ℕ} (hj : j < n) : ω j = ω' j := by
  have hj' : j < (streamTake ω n).length := by simpa using hj
  rw [← getElem_streamTake ω n j hj', h.getElem hj', getElem_streamTake]

@[simp] theorem streamTake_zero (ω : ℕ → α) : streamTake ω 0 = [] := rfl

end Stream

/-- A path from a busy position along lower moves only stays busy. -/
theorem path_ne_idle {F : Sig.{u}} {x y : Pos E F} {u : List (Move E F)} (h : Path x u y)
    (hx : x ≠ .idle) (hu : ∀ e, (.inr e : Move E F) ∉ u) : y ≠ .idle := by
  induction h with
  | nil => exact hx
  | cons hs _ ih =>
    refine ih ?_ fun e he => hu e (List.mem_cons_of_mem _ he)
    cases hs with
    | ask => exact absurd rfl hx
    | call => simp
    | reply => simp
    | ret => exact absurd List.mem_cons_self (hu _)

/-! ## Stream plays -/

section StreamPlay

theorem isInfPlay_streamPlay (pre : List (Move E (sig1 A B))) (a : A) (ω : ℕ → Call E) :
    IsInfPlay (streamPlay pre a ω) := by
  refine Chain.isInfPlay_lim (c := fun k => pre ++ .inr (.ask a) :: callMoves (streamTake ω k))
    (fun k => ⟨callMoves [ω k], by simp [streamTake_succ]⟩) fun k => ⟨k, ?_⟩
  simp [length_callMoves]
  omega

theorem ask_inj_of_prefix {pre pre' : List (Move E (sig1 A B))} {a a' : A} {cm : List (Call E)}
    (h₁ : pre ++ [.inr (.ask a)] <+: pre' ++ [.inr (.ask a')])
    (h₂ : pre' ++ [.inr (.ask a')] <+: pre ++ .inr (.ask a) :: callMoves cm) :
    pre = pre' ∧ a = a' := by
  rcases List.prefix_concat_iff.1 h₁ with h | h
  · obtain ⟨h₃, h₄⟩ := List.append_inj' h rfl
    simp only [List.cons.injEq, Sum.inr.injEq, Ev.ask.injEq, and_true] at h₄
    exact ⟨h₃, h₄⟩
  · obtain ⟨x, rfl⟩ := h
    simp only [List.append_assoc, List.prefix_append_right_inj, List.cons_append,
      List.cons_prefix_cons, true_and] at h₂
    exact (not_inr_mem_callMoves
      (h₂.subset (by simp : (Sum.inr (Ev.ask a') : Move E (sig1 A B)) ∈ x ++ [_]))).elim

theorem streamPlay_eq {pre pre' : List (Move E (sig1 A B))} {a a' : A} {ω ω' : ℕ → Call E}
    (h : streamPlay pre a ω = streamPlay pre' a' ω') : pre = pre' ∧ a = a' ∧ ω = ω' := by
  have m₁ : pre ++ [.inr (.ask a)] ∈ streamPlay pre' a' ω' := h ▸ ⟨0, by simp⟩
  have m₂ : pre' ++ [.inr (.ask a')] ∈ streamPlay pre a ω := h ▸ ⟨0, by simp⟩
  obtain ⟨k₁, hk₁⟩ := m₁
  obtain ⟨k₂, hk₂⟩ := m₂
  have hpa : pre = pre' ∧ a = a' := by
    rcases List.prefix_or_prefix_of_prefix hk₁
        (show pre' ++ [.inr (.ask a')] <+: pre' ++ .inr (.ask a') :: callMoves (streamTake ω' k₁)
          by simp) with h' | h'
    · exact ask_inj_of_prefix h' hk₂
    · obtain ⟨e₁, e₂⟩ := ask_inj_of_prefix h' hk₁
      exact ⟨e₁.symm, e₂.symm⟩
  obtain ⟨rfl, rfl⟩ := hpa
  refine ⟨rfl, rfl, funext fun j => ?_⟩
  have : (pre ++ .inr (.ask a) :: callMoves (streamTake ω (j + 1)) : List (Move E (sig1 A B))) ∈
      streamPlay pre a ω' := h ▸ ⟨j + 1, List.prefix_refl _⟩
  obtain ⟨k, hk⟩ := this
  simp only [List.prefix_append_right_inj, List.cons_prefix_cons, true_and] at hk
  exact eq_of_streamTake_prefix (prefix_of_callMoves hk) (Nat.lt_succ_self j)

/-- A completed round inside a stream play lies within its completed rounds. -/
theorem prefix_pre_of_ans {pre u : List (Move E (sig1 A B))} {a a' : A} {r : B ⊕ PUnit}
    {cm : List (Call E)}
    (h : u ++ [.inr (.ans a r)] <+: pre ++ .inr (.ask a') :: callMoves cm) :
    u ++ [.inr (.ans a r)] <+: pre := by
  have h₂ : pre ++ [.inr (.ask a')] <+: pre ++ .inr (.ask a') :: callMoves cm := by simp
  rcases List.prefix_or_prefix_of_prefix h h₂ with h₃ | ⟨x, hx⟩
  · rcases List.prefix_concat_iff.1 h₃ with h₄ | h₄
    · have := congrArg List.getLast? h₄
      simp at this
    · exact h₄
  · rw [← hx] at h
    simp only [List.append_assoc, List.prefix_append_right_inj, List.singleton_append,
      List.cons_prefix_cons, true_and] at h
    rcases List.eq_nil_or_concat x with rfl | ⟨L, o, rfl⟩
    · have := congrArg List.getLast? hx
      simp at this
    · have := congrArg List.getLast? hx
      simp only [List.concat_eq_append, ← List.append_assoc, List.getLast?_append,
        List.getLast?_singleton, Option.some_or, Option.some.injEq] at this
      subst this
      exact (not_inr_mem_callMoves
        (h.subset (by simp : (Sum.inr (Ev.ans a r) : Move E (sig1 A B)) ∈ L.concat _))).elim

end StreamPlay

/-! ## Reading the calls of a round -/

section Read

variable {f : AFun E S A B} {P : Pending E S A}

theorem readCalls (s : S) (a : A) {c₀ c : List (Call E)}
    (h : ∀ c₁ x c₂, c = c₁ ++ x :: c₂ → (c₀ ++ c₁, x.1) ∈ P s a) :
    TRun f P (.run s a c₀) (callMoves c) (.run s a (c₀ ++ c)) := by
  induction c generalizing c₀ with
  | nil => simpa using TRun.nil _
  | cons x c ih =>
    have h₀ := h [] x c rfl
    simp only [List.append_nil] at h₀
    refine .cons (.call s a c₀ x.1 h₀) (.cons (.reply s a c₀ x.1 x.2) ?_)
    have := ih (c₀ := c₀ ++ [x]) fun c₁ y c₂ hc => by
      simpa using h (x :: c₁) y c₂ (by simp [hc])
    rw [show c₀ ++ x :: c = c₀ ++ [x] ++ c by simp]
    exact this

theorem readCalls_inv {s : S} {a : A} {c₀ c : List (Call E)} {u : List (Move E (sig1 A B))}
    {y : TSt E S A} (h : TRun f P (.run s a c₀) (callMoves c ++ u) y) :
    (∀ c₁ x c₂, c = c₁ ++ x :: c₂ → (c₀ ++ c₁, x.1) ∈ P s a) ∧
      TRun f P (.run s a (c₀ ++ c)) u y := by
  induction c generalizing c₀ with
  | nil => exact ⟨fun c₁ x c₂ h => by simp at h, by simpa using h⟩
  | cons x c ih =>
    obtain ⟨m, n⟩ := x
    simp only [callMoves_cons, List.cons_append] at h
    cases h with
    | cons h₁ h₂ =>
      cases h₁ with
      | call _ _ _ _ hP =>
        cases h₂ with
        | cons h₃ h₄ =>
          cases h₃ with
          | reply =>
            obtain ⟨ih₁, ih₂⟩ := ih h₄
            refine ⟨fun c₁ x c₂ hc => ?_, by simpa using ih₂⟩
            cases c₁ with
            | nil => simp at hc; obtain ⟨rfl, -⟩ := hc; simpa using hP
            | cons z c₁ =>
              simp only [List.cons_append, List.cons.injEq] at hc
              obtain ⟨rfl, hc⟩ := hc
              simpa using ih₁ c₁ x c₂ hc

theorem stuck_inv {a : A} {u : List (Move E (sig1 A B))} {y : TSt E S A}
    (h : TRun f P (.stuck a) u y) : u = [] ∧ y = .stuck a := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | cons h _ => cases h

theorem dead_inv {u : List (Move E (sig1 A B))} {y : TSt E S A} :
    TRun f P .dead u y ↔ (u = [] ∧ y = .dead) ∨ ∃ a, u = [.inr (.ask a)] ∧ y = .stuck a := by
  constructor
  · intro h
    cases h with
    | nil => exact .inl ⟨rfl, rfl⟩
    | cons h₁ h₂ =>
      cases h₁ with
      | deadAsk a =>
        obtain ⟨rfl, rfl⟩ := stuck_inv h₂
        exact .inr ⟨a, rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨a, rfl, rfl⟩)
    · exact .nil _
    · exact .cons (.deadAsk a) (.nil _)

/-- After a question and lower moves only, the automaton is not idle. -/
theorem not_idle_after_ask {x₀ : TSt E S A} {pre x : List (Move E (sig1 A B))} {a : A} {s : S}
    (h : TRun f P x₀ (pre ++ [.inr (.ask a)] ++ x) (.idle s))
    (hx : ∀ e, (.inr e : Move E (sig1 A B)) ∉ x) : False := by
  obtain ⟨y, h₁, h₂⟩ := h.of_append
  obtain ⟨y₀, -, h₃⟩ := h₁.of_append
  have hy : (y.pos : Pos E (sig1 A B)) ≠ .idle := by
    cases h₃ with
    | cons h₄ h₅ => cases h₅; cases h₄ <;> simp [TSt.pos]
  exact path_ne_idle h₂.pos hy hx rfl

end Read

/-! ## Saturation -/

section Sat

variable {t : ObsTriple E S A B}

theorem satP_of_beh {s : S} {a : A} {d c₁ c₂ : List (Call E)} {x : Call E} {e : End S B}
    (h : (d, e) ∈ t.1 s a) (hd : d = c₁ ++ x :: c₂) : (c₁, x.1) ∈ satP t s a :=
  .inr (.inr (.inl ⟨d, e, h, x.2, c₂, hd⟩))

theorem satP_of_stream {s : S} {a : A} {ω : ℕ → Call E} (hω : ω ∈ t.2.2 s a) {k : ℕ}
    {c₁ c₂ : List (Call E)} {x : Call E} (hk : streamTake ω k = c₁ ++ x :: c₂) :
    (c₁, x.1) ∈ satP t s a := by
  obtain ⟨h₁, h₂⟩ := streamTake_eq_append hk
  exact .inr (.inr (.inr ⟨ω, hω, c₁.length, h₁, by simp [h₂]⟩))

end Sat

/-! ## Reading rounds -/

section Rounds

variable {t : ObsTriple E S A B}

theorem readCalls_beh {s : S} {a : A} {d : List (Call E)} {e : End S B} (h : (d, e) ∈ t.1 s a) :
    TRun t.1 (satP t) (.run s a []) (callMoves d) (.run s a d) := by
  simpa using readCalls (f := t.1) (P := satP t) s a (c₀ := []) fun c₁ x c₂ hc => by
    simpa using satP_of_beh h hc

theorem ask_calls_inv {s : S} {a : A} {c : List (Call E)} {u : List (Move E (sig1 A B))}
    {y : TSt E S A} :
    TRun t.1 (satP t) (.idle s) (.inr (.ask a) :: (callMoves c ++ u)) y ↔
      (∀ c₁ x c₂, c = c₁ ++ x :: c₂ → (c₁, x.1) ∈ satP t s a) ∧
        TRun t.1 (satP t) (.run s a c) u y := by
  constructor
  · intro h
    cases h with
    | cons h₁ h₂ =>
      cases h₁
      obtain ⟨h₃, h₄⟩ := readCalls_inv h₂
      exact ⟨fun c₁ x c₂ hc => by simpa using h₃ c₁ x c₂ hc, by simpa using h₄⟩
  · rintro ⟨h₁, h₂⟩
    refine .cons (.ask s a) ((readCalls s a (c₀ := []) fun c₁ x c₂ hc => ?_).append (by simpa))
    simpa using h₁ c₁ x c₂ hc

theorem round_inv {s : S} {r : A × List (Call E) × B} {u : List (Move E (sig1 A B))}
    {y : TSt E S A} :
    TRun t.1 (satP t) (.idle s) (roundMoves r ++ u) y ↔
      ∃ s₁, (r.2.1, .ret r.2.2 s₁) ∈ t.1 s r.1 ∧ TRun t.1 (satP t) (.idle s₁) u y := by
  obtain ⟨a, c, b⟩ := r
  simp only [roundMoves, List.cons_append, List.append_assoc]
  constructor
  · intro h
    obtain ⟨-, h⟩ := ask_calls_inv.1 h
    cases h with
    | cons h₃ h₄ => cases h₃ with | ret _ _ _ _ s₁ hr => exact ⟨s₁, hr, h₄⟩
  · rintro ⟨s₁, hr, hu⟩
    exact .cons (.ask s a) ((readCalls_beh hr).append (.cons (.ret s a c b s₁ hr) hu))

theorem rounds_inv {s : S} {rs : List (A × List (Call E) × B)} {u : List (Move E (sig1 A B))}
    {y : TSt E S A} :
    TRun t.1 (satP t) (.idle s) (roundsMoves rs ++ u) y ↔
      ∃ s₁, Rounds t s rs s₁ ∧ TRun t.1 (satP t) (.idle s₁) u y := by
  induction rs generalizing s with
  | nil => exact ⟨fun h => ⟨s, .nil s, h⟩, fun ⟨_, h₁, h₂⟩ => by cases h₁; exact h₂⟩
  | cons r rs ih =>
    obtain ⟨a, c, b⟩ := r
    rw [show roundsMoves ((a, c, b) :: rs) ++ u = roundMoves (a, c, b) ++ (roundsMoves rs ++ u) by
      simp [roundsMoves], round_inv]
    constructor
    · rintro ⟨s₁, h₁, h₂⟩
      obtain ⟨s₂, h₃, h₄⟩ := ih.1 h₂
      exact ⟨s₂, .cons h₁ h₃, h₄⟩
    · rintro ⟨s₂, h₁, h₂⟩
      cases h₁ with
      | cons h₃ h₄ => exact ⟨_, h₃, ih.2 ⟨_, h₄, h₂⟩⟩

theorem trap_inv {s : S} {a : A} {c : List (Call E)} {u : List (Move E (sig1 A B))}
    {y : TSt E S A} :
    TRun t.1 (satP t) (.idle s) (trapMoves a c ++ u) y ↔
      (c, .trap) ∈ t.1 s a ∧ TRun t.1 (satP t) .dead u y := by
  simp only [trapMoves, List.cons_append, List.append_assoc]
  constructor
  · intro h
    obtain ⟨-, h⟩ := ask_calls_inv.1 h
    cases h with
    | cons h₃ h₄ => cases h₃ with | trap _ _ _ hr => exact ⟨hr, h₄⟩
  · rintro ⟨hr, hu⟩
    exact .cons (.ask s a) ((readCalls_beh hr).append (.cons (.trap s a c hr) hu))

theorem pending_inv {s : S} {a : A} {c : List (Call E)} {m : E.Op} {y : TSt E S A} :
    TRun t.1 (satP t) (.idle s) (.inr (.ask a) :: (callMoves c ++ [.inl (.ask m)])) y ↔
      (c, m) ∈ satP t s a ∧ y = .wait s a c m := by
  rw [ask_calls_inv]
  constructor
  · rintro ⟨-, h⟩
    cases h with
    | cons h₁ h₂ => cases h₁ with | call _ _ _ _ hP => cases h₂; exact ⟨hP, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨fun c₁ x c₂ hc => satP_prefix h ⟨x.2, c₂, hc⟩, .cons (.call s a c m h) (.nil _)⟩

/-! ### Membership in the threaded strategy -/

variable {s₀ : S}

theorem mem_append_rounds {rs : List (A × List (Call E) × B)} {p : List (Move E (sig1 A B))} :
    roundsMoves rs ++ p ∈ (threadT t s₀).toStrategy ↔
      ∃ s, Rounds t s₀ rs s ∧ p ∈ (threadT t s).toStrategy := by
  constructor
  · rintro ⟨y, h⟩
    obtain ⟨s, h₁, h₂⟩ := rounds_inv.1 h
    exact ⟨s, h₁, y, h₂⟩
  · rintro ⟨s, h₁, y, h₂⟩
    exact ⟨y, rounds_inv.2 ⟨s, h₁, h₂⟩⟩

theorem div_append_rounds {rs : List (A × List (Call E) × B)} {p : List (Move E (sig1 A B))} :
    roundsMoves rs ++ p ∈ (threadT t s₀).div ↔ ∃ s, Rounds t s₀ rs s ∧ p ∈ (threadT t s).div := by
  constructor
  · rintro ⟨s, a, c, h, hd⟩
    obtain ⟨s₁, h₁, h₂⟩ := rounds_inv.1 h
    exact ⟨s₁, h₁, s, a, c, h₂, hd⟩
  · rintro ⟨s₁, h₁, s, a, c, h₂, hd⟩
    exact ⟨s, a, c, rounds_inv.2 ⟨s₁, h₁, h₂⟩, hd⟩

theorem mem_rounds {rs : List (A × List (Call E) × B)} :
    roundsMoves rs ∈ (threadT t s₀).toStrategy ↔ ∃ s, Rounds t s₀ rs s := by
  rw [← List.append_nil (roundsMoves rs), mem_append_rounds]
  exact ⟨fun ⟨s, h, _⟩ => ⟨s, h⟩, fun ⟨s, h⟩ => ⟨s, h, (threadT t s).toStrategy.nil_mem⟩⟩

theorem mem_trap₁ {s : S} {a : A} {c : List (Call E)} {u : List (Move E (sig1 A B))} :
    trapMoves a c ++ u ∈ (threadT t s).toStrategy ↔
      (c, .trap) ∈ t.1 s a ∧ (u = [] ∨ ∃ a', u = [.inr (.ask a')]) := by
  constructor
  · rintro ⟨y, h⟩
    obtain ⟨h₁, h₂⟩ := trap_inv.1 h
    refine ⟨h₁, ?_⟩
    rcases dead_inv.1 h₂ with ⟨rfl, -⟩ | ⟨a', rfl, -⟩
    · exact .inl rfl
    · exact .inr ⟨a', rfl⟩
  · rintro ⟨h₁, h₂⟩
    rcases h₂ with rfl | ⟨a', rfl⟩
    · exact ⟨_, trap_inv.2 ⟨h₁, .nil _⟩⟩
    · exact ⟨_, trap_inv.2 ⟨h₁, .cons (.deadAsk a') (.nil _)⟩⟩

theorem mem_trap {rs : List (A × List (Call E) × B)} {a : A} {c : List (Call E)}
    {u : List (Move E (sig1 A B))} :
    roundsMoves rs ++ (trapMoves a c ++ u) ∈ (threadT t s₀).toStrategy ↔
      (∃ s, Rounds t s₀ rs s ∧ (c, .trap) ∈ t.1 s a) ∧ (u = [] ∨ ∃ a', u = [.inr (.ask a')]) := by
  rw [mem_append_rounds]
  simp only [mem_trap₁]
  exact ⟨fun ⟨s, h₁, h₂, h₃⟩ => ⟨⟨s, h₁, h₂⟩, h₃⟩, fun ⟨⟨s, h₁, h₂⟩, h₃⟩ => ⟨s, h₁, h₂, h₃⟩⟩

theorem mem_pending₁ {s : S} {a : A} {c : List (Call E)} {m : E.Op} :
    (.inr (.ask a) :: (callMoves c ++ [.inl (.ask m)]) : List (Move E (sig1 A B))) ∈
      (threadT t s).toStrategy ↔ (c, m) ∈ satP t s a :=
  ⟨fun ⟨_, h⟩ => (pending_inv.1 h).1, fun h => ⟨_, pending_inv.2 ⟨h, rfl⟩⟩⟩

theorem mem_pending {rs : List (A × List (Call E) × B)} {a : A} {c : List (Call E)} {m : E.Op} :
    roundsMoves rs ++ .inr (.ask a) :: (callMoves c ++ [.inl (.ask m)]) ∈
      (threadT t s₀).toStrategy ↔ ∃ s, Rounds t s₀ rs s ∧ (c, m) ∈ satP t s a := by
  rw [mem_append_rounds]
  simp only [mem_pending₁]

theorem mem_div₁ {s : S} {a : A} {c : List (Call E)} :
    (.inr (.ask a) :: callMoves c : List (Move E (sig1 A B))) ∈ (threadT t s).div ↔
      (c, .div) ∈ t.1 s a := by
  constructor
  · rintro ⟨s', a', c', h, hd⟩
    rw [← List.append_nil (callMoves c)] at h
    obtain ⟨-, h⟩ := ask_calls_inv.1 h
    cases h
    exact hd
  · intro h
    refine ⟨s, a, c, ?_, h⟩
    rw [← List.append_nil (callMoves c)]
    exact ask_calls_inv.2 ⟨fun c₁ x c₂ hc => satP_of_beh h hc, .nil _⟩

theorem mem_div {rs : List (A × List (Call E) × B)} {a : A} {c : List (Call E)} :
    roundsMoves rs ++ .inr (.ask a) :: callMoves c ∈ (threadT t s₀).div ↔
      ∃ s, Rounds t s₀ rs s ∧ (c, .div) ∈ t.1 s a := by
  rw [div_append_rounds]
  simp only [mem_div₁]

theorem streamPlay_mem {pre : List (Move E (sig1 A B))} {s : S} {a : A} {ω : ℕ → Call E}
    (hpre : TRun t.1 (satP t) (.idle s₀) pre (.idle s)) (hω : ω ∈ t.2.2 s a) :
    streamPlay pre a ω ∈ (threadT t s₀).inf := by
  refine ⟨isInfPlay_streamPlay pre a ω, ?_, .inl ⟨pre, s, a, ω, hpre, hω, rfl⟩⟩
  rintro p ⟨k, hp⟩
  refine (threadT t s₀).toStrategy.of_prefix ?_ hp
  refine ⟨_, hpre.append (.cons (.ask s a) (readCalls (c₀ := []) s a fun c₁ x c₂ hc => ?_))⟩
  simpa using satP_of_stream hω hc

theorem mem_inf {rs : List (A × List (Call E) × B)} {a : A} {ω : ℕ → Call E} :
    streamPlay (roundsMoves rs) a ω ∈ (threadT t s₀).inf ↔
      ∃ s, Rounds t s₀ rs s ∧ ω ∈ t.2.2 s a := by
  constructor
  · rintro ⟨-, -, ⟨pre, s, a', ω', hpre, hω', hI⟩ | h⟩
    · obtain ⟨rfl, rfl, rfl⟩ := streamPlay_eq hI
      rw [← List.append_nil (roundsMoves rs)] at hpre
      obtain ⟨s₁, h₁, h₂⟩ := rounds_inv.1 hpre
      cases h₂
      exact ⟨s, h₁, hω'⟩
    · obtain ⟨p', hp', hpre, s, hrun⟩ := h (roundsMoves rs ++ [.inr (.ask a)]) ⟨0, by simp⟩
      obtain ⟨k, hk⟩ := hp'
      obtain ⟨x, rfl⟩ := hpre
      simp only [List.append_assoc, List.prefix_append_right_inj, List.singleton_append,
        List.cons_prefix_cons, true_and] at hk
      exact (not_idle_after_ask hrun fun e he => not_inr_mem_callMoves (hk.subset he)).elim
  · rintro ⟨s, h₁, h₂⟩
    refine streamPlay_mem ?_ h₂
    rw [← List.append_nil (roundsMoves rs)]
    exact rounds_inv.2 ⟨s, h₁, .nil _⟩

theorem mem_inf₁ {s : S} {a : A} {ω : ℕ → Call E} :
    streamPlay [] a ω ∈ (threadT t s).inf ↔ ω ∈ t.2.2 s a := by
  have := mem_inf (t := t) (s₀ := s) (rs := []) (a := a) (ω := ω)
  refine this.trans ⟨fun ⟨s', h₁, h₂⟩ => ?_, fun h => ⟨s, .nil s, h⟩⟩
  cases h₁
  exact h₂

theorem mem_roundMoves {s : S} {a : A} {c : List (Call E)} {b : B} :
    roundMoves (a, c, b) ∈ (threadT t s).toStrategy ↔ ∃ s₁, (c, .ret b s₁) ∈ t.1 s a := by
  constructor
  · rintro ⟨y, h⟩
    rw [← List.append_nil (roundMoves _)] at h
    obtain ⟨s₁, h₁, -⟩ := round_inv.1 h
    exact ⟨s₁, h₁⟩
  · rintro ⟨s₁, h⟩
    refine ⟨.idle s₁, ?_⟩
    rw [← List.append_nil (roundMoves _)]
    exact round_inv.2 ⟨s₁, h, .nil _⟩

end Rounds

/-! ## Reachable stores -/

section Reach

variable {t : ObsTriple E S A B}

theorem reach_tail {s₀ s s₁ : S} {a : A} {c : List (Call E)} {b : B} (h : Reach t s₀ s)
    (hr : (c, .ret b s₁) ∈ t.1 s a) : Reach t s₀ s₁ := by
  induction h with
  | refl => exact .step hr (.refl _)
  | step h₀ _ ih => exact .step h₀ (ih hr)

theorem reach_iff {s₀ s : S} : Reach t s₀ s ↔ ∃ rs, Rounds t s₀ rs s := by
  constructor
  · intro h
    induction h with
    | refl s => exact ⟨[], .nil s⟩
    | @step s s₁ s₂ a c b h₀ _ ih =>
      obtain ⟨rs, hrs⟩ := ih
      exact ⟨(a, c, b) :: rs, .cons h₀ hrs⟩
  · rintro ⟨rs, h⟩
    induction h with
    | nil s => exact .refl s
    | cons h₀ _ ih => exact .step h₀ ih

end Reach

/-! ## Bisimulation soundness -/

section Bisim

variable {S' : Type u} {t : ObsTriple E S A B} {t' : ObsTriple E S' A B}

/-- Related automaton states: the same shape, with related stores. -/
inductive LiftR (R : S → S' → Prop) : TSt E S A → TSt E S' A → Prop
  | idle {s : S} {s' : S'} : R s s' → LiftR R (.idle s) (.idle s')
  | run {s : S} {s' : S'} (a : A) (c : List (Call E)) : R s s' → LiftR R (.run s a c) (.run s' a c)
  | wait {s : S} {s' : S'} (a : A) (c : List (Call E)) (m : E.Op) :
      R s s' → LiftR R (.wait s a c m) (.wait s' a c m)
  | dead : LiftR R .dead .dead
  | stuck (a : A) : LiftR R (.stuck a) (.stuck a)

theorem isBisim_flip {R : S → S' → Prop} (hR : IsBisim t t' R) :
    IsBisim t' t (fun s' s => R s s') := fun s s' h =>
  let H := hR s' s h
  { trap := fun a c => (H.trap a c).symm
    div := fun a c => (H.div a c).symm
    pend := H.pend.symm
    inf := H.inf.symm
    ret := H.ret'
    ret' := H.ret }

theorem step_sim {R : S → S' → Prop} (hR : IsBisim t t' R) {x y : TSt E S A} {x' : TSt E S' A}
    {o : Move E (sig1 A B)} (hx : LiftR R x x') (h : TStep t.1 (satP t) x o y) :
    ∃ y', TStep t'.1 (satP t') x' o y' ∧ LiftR R y y' := by
  cases h with
  | ask s a => cases hx with | idle h => exact ⟨_, .ask _ a, .run a [] h⟩
  | call s a c m hP =>
    cases hx with
    | run _ _ h => exact ⟨_, .call _ a c m (by rw [← (hR _ _ h).pend]; exact hP), .wait a c m h⟩
  | reply s a c m n => cases hx with | wait _ _ _ h => exact ⟨_, .reply _ a c m n, .run _ _ h⟩
  | ret s a c b s₁ hr =>
    cases hx with
    | run _ _ h =>
      obtain ⟨s₁', h₁, h₂⟩ := (hR _ _ h).ret a c b s₁ hr
      exact ⟨_, .ret _ a c b s₁' h₁, .idle h₂⟩
  | trap s a c hr =>
    cases hx with | run _ _ h => exact ⟨_, .trap _ a c (((hR _ _ h).trap a c).1 hr), .dead⟩
  | deadAsk a => cases hx with | dead => exact ⟨_, .deadAsk a, .stuck a⟩

theorem run_sim {R : S → S' → Prop} (hR : IsBisim t t' R) {x y : TSt E S A} {x' : TSt E S' A}
    {p : List (Move E (sig1 A B))} (hx : LiftR R x x') (h : TRun t.1 (satP t) x p y) :
    ∃ y', TRun t'.1 (satP t') x' p y' ∧ LiftR R y y' := by
  induction h generalizing x' with
  | nil => exact ⟨x', .nil _, hx⟩
  | cons h _ ih =>
    obtain ⟨z', h₁, h₂⟩ := step_sim hR hx h
    obtain ⟨y', h₃, h₄⟩ := ih h₂
    exact ⟨y', .cons h₁ h₃, h₄⟩

theorem plays_sub {R : S → S' → Prop} (hR : IsBisim t t' R) {s : S} {s' : S'} (h : R s s')
    {p : List (Move E (sig1 A B))} (hp : p ∈ (threadT t s).toStrategy) :
    p ∈ (threadT t' s').toStrategy := by
  obtain ⟨y, hy⟩ := hp
  obtain ⟨y', h₁, -⟩ := run_sim hR (.idle h) hy
  exact ⟨y', h₁⟩

theorem divs_sub {R : S → S' → Prop} (hR : IsBisim t t' R) {s : S} {s' : S'} (h : R s s') :
    (threadT t s).div ⊆ (threadT t' s').div := by
  rintro p ⟨s₁, a, c, hp, hd⟩
  obtain ⟨y', h₁, h₂⟩ := run_sim hR (.idle h) hp
  cases h₂ with
  | run _ _ h₃ => exact ⟨_, a, c, h₁, ((hR _ _ h₃).div a c).1 hd⟩

theorem infs_sub {R : S → S' → Prop} (hR : IsBisim t t' R) {s : S} {s' : S'} (h : R s s') :
    (threadT t s).inf ⊆ (threadT t' s').inf := by
  rintro I ⟨hI, hsub, hk⟩
  refine ⟨hI, fun p hp => plays_sub hR h (hsub hp), ?_⟩
  rcases hk with ⟨pre, s₁, a, ω, hpre, hω, rfl⟩ | hk
  · obtain ⟨y', h₁, h₂⟩ := run_sim hR (.idle h) hpre
    cases h₂ with
    | idle h₃ => exact .inl ⟨pre, _, a, ω, h₁, by rw [← (hR _ _ h₃).inf]; exact hω, rfl⟩
  · refine .inr fun p hp => ?_
    obtain ⟨p', hp', hpp', s₂, hrun⟩ := hk p hp
    obtain ⟨y', h₁, h₂⟩ := run_sim hR (.idle h) hrun
    cases h₂ with
    | idle => exact ⟨p', hp', hpp', _, h₁⟩

theorem threadT_eq_of_isBisim {R : S → S' → Prop} (hR : IsBisim t t' R) {s : S} {s' : S'}
    (h : R s s') : threadT t s = threadT t' s' :=
  DStrategy.ext
    (Strategy.ext fun _ => ⟨plays_sub hR h, plays_sub (isBisim_flip hR) h⟩)
    ((divs_sub hR h).antisymm (divs_sub (isBisim_flip hR) h))
    ((infs_sub hR h).antisymm (infs_sub (isBisim_flip hR) h))

end Bisim

/-! ## Congruence on reachable stores -/

theorem threadT_congr {t t' : ObsTriple E S A B} {s₀ : S}
    (h : ∀ s, Reach t s₀ s → t.1 s = t'.1 s ∧ satP t s = satP t' s ∧ t.2.2 s = t'.2.2 s) :
    threadT t s₀ = threadT t' s₀ := by
  refine threadT_eq_of_isBisim (R := fun s s' => s = s' ∧ Reach t s₀ s) ?_ ⟨rfl, .refl s₀⟩
  rintro s _ ⟨rfl, hs⟩
  obtain ⟨h₁, h₂, h₃⟩ := h s hs
  exact
    { trap := fun a c => by rw [h₁]
      div := fun a c => by rw [h₁]
      pend := h₂
      inf := h₃
      ret := fun a c b s₁ hr => ⟨s₁, by rw [← h₁]; exact hr, rfl, reach_tail hs hr⟩
      ret' := fun a c b s₁ hr => by
        rw [← h₁] at hr
        exact ⟨s₁, hr, rfl, reach_tail hs hr⟩ }

/-! ## Residuals after a round, for store-deterministic triples -/

section Residual

variable {α : Type u}

/-- The trace `I` after the round `r`, with the prefixes of `r`. -/
def extR (r : List α) (I : Set (List α)) : Set (List α) := {q | q <+: r ∨ ∃ p ∈ I, q = r ++ p}

/-- The residual of the trace `J` after `r`. -/
def resR (r : List α) (J : Set (List α)) : Set (List α) := {p | r ++ p ∈ J}

theorem isInfPlay_extR {r : List α} {I : Set (List α)} (hI : IsInfPlay I) :
    IsInfPlay (extR r I) where
  of_prefix := by
    rintro q₀ q (hq | ⟨p, hp, rfl⟩) h
    · exact .inl (h.trans hq)
    · rcases prefix_append_iff.1 h with h' | ⟨p', rfl, h'⟩
      · exact .inl h'
      · exact .inr ⟨p', hI.of_prefix hp h', rfl⟩
  total := by
    rintro q₁ q₂ (h₁ | ⟨p₁, hp₁, rfl⟩) (h₂ | ⟨p₂, hp₂, rfl⟩)
    · exact List.prefix_or_prefix_of_prefix h₁ h₂
    · exact .inl (List.prefix_append_of_prefix h₁)
    · exact .inr (List.prefix_append_of_prefix h₂)
    · rcases hI.total hp₁ hp₂ with h | h
      · exact .inl ((List.prefix_append_right_inj r).2 h)
      · exact .inr ((List.prefix_append_right_inj r).2 h)
  unbounded k := by
    obtain ⟨p, hp, hk⟩ := hI.unbounded k
    exact ⟨r ++ p, .inr ⟨p, hp, rfl⟩, by simp; omega⟩

theorem resR_extR {r : List α} {I : Set (List α)} (hI : IsInfPlay I) : resR r (extR r I) = I := by
  ext p
  show (r ++ p <+: r ∨ ∃ p' ∈ I, r ++ p = r ++ p') ↔ p ∈ I
  simp only [List.append_cancel_left_eq, exists_eq_right']
  constructor
  · rintro (h | h)
    · obtain ⟨q, hq, -⟩ := hI.unbounded 0
      have hp : p = [] := by
        simpa using (List.prefix_append_right_inj r (l₂ := [])).1 (by simpa using h)
      exact hp ▸ hI.of_prefix hq List.nil_prefix
    · exact h
  · exact .inr

theorem extR_streamPlay (r pre : List (Move E (sig1 A B))) (a : A) (ω : ℕ → Call E) :
    extR r (streamPlay pre a ω) = streamPlay (r ++ pre) a ω := by
  ext q
  constructor
  · rintro (h | ⟨p, ⟨k, hk⟩, rfl⟩)
    · exact ⟨0, (h.trans (List.prefix_append _ _)).trans (List.prefix_append _ _)⟩
    · exact ⟨k, by simpa [List.append_assoc] using hk⟩
  · rintro ⟨k, hk⟩
    rw [List.append_assoc] at hk
    rcases prefix_append_iff.1 hk with h | ⟨p', rfl, h⟩
    · exact .inl h
    · exact .inr ⟨p', ⟨k, h⟩, rfl⟩

theorem resR_streamPlay (r pre : List (Move E (sig1 A B))) (a : A) (ω : ℕ → Call E) :
    resR r (streamPlay (r ++ pre) a ω) = streamPlay pre a ω := by
  ext p
  show (∃ k, r ++ p <+: (r ++ pre) ++ _) ↔ ∃ k, p <+: pre ++ _
  simp only [List.append_assoc, List.prefix_append_right_inj]

variable {t : ObsTriple E S A B} {s s₁ : S} {a : A} {c : List (Call E)} {b : B}

theorem round_det (ht : StoreDet t) (hr : (c, .ret b s₁) ∈ t.1 s a)
    {u : List (Move E (sig1 A B))} {y : TSt E S A} :
    TRun t.1 (satP t) (.idle s) (roundMoves (a, c, b) ++ u) y ↔
      TRun t.1 (satP t) (.idle s₁) u y := by
  rw [round_inv]
  constructor
  · rintro ⟨s₂, h₁, h₂⟩
    rwa [ht s a c b s₁ s₂ hr h₁]
  · exact fun h => ⟨s₁, hr, h⟩

theorem round_run (hr : (c, .ret b s₁) ∈ t.1 s a) :
    TRun t.1 (satP t) (.idle s) (roundMoves (a, c, b)) (.idle s₁) := by
  rw [← List.append_nil (roundMoves _)]
  exact round_inv.2 ⟨s₁, hr, .nil _⟩

theorem mem_after_round (ht : StoreDet t) (hr : (c, .ret b s₁) ∈ t.1 s a)
    {p : List (Move E (sig1 A B))} :
    roundMoves (a, c, b) ++ p ∈ (threadT t s).toStrategy ↔ p ∈ (threadT t s₁).toStrategy :=
  ⟨fun ⟨y, h⟩ => ⟨y, (round_det ht hr).1 h⟩, fun ⟨y, h⟩ => ⟨y, (round_det ht hr).2 h⟩⟩

theorem div_after_round (ht : StoreDet t) (hr : (c, .ret b s₁) ∈ t.1 s a)
    {p : List (Move E (sig1 A B))} :
    roundMoves (a, c, b) ++ p ∈ (threadT t s).div ↔ p ∈ (threadT t s₁).div :=
  ⟨fun ⟨s', a', c', h, hd⟩ => ⟨s', a', c', (round_det ht hr).1 h, hd⟩,
    fun ⟨s', a', c', h, hd⟩ => ⟨s', a', c', (round_det ht hr).2 h, hd⟩⟩

theorem extR_mem_inf (hr : (c, .ret b s₁) ∈ t.1 s a) {I : Set (List (Move E (sig1 A B)))}
    (hI : I ∈ (threadT t s₁).inf) : extR (roundMoves (a, c, b)) I ∈ (threadT t s).inf := by
  obtain ⟨hI, hsub, hk⟩ := hI
  have hrun := round_run hr
  refine ⟨isInfPlay_extR hI, ?_, ?_⟩
  · rintro q (hq | ⟨p, hp, rfl⟩)
    · exact (threadT t s).toStrategy.of_prefix ⟨_, hrun⟩ hq
    · obtain ⟨y, hy⟩ := hsub hp
      exact ⟨y, hrun.append hy⟩
  · rcases hk with ⟨pre, s₂, a', ω, hpre, hω, rfl⟩ | hk
    · exact .inl ⟨_, s₂, a', ω, hrun.append hpre, hω, extR_streamPlay _ _ _ _⟩
    · refine .inr ?_
      rintro q (hq | ⟨p, hp, rfl⟩)
      · exact ⟨_, .inl (List.prefix_refl _), hq, s₁, hrun⟩
      · obtain ⟨p', hp', hpp', s₂, hrun'⟩ := hk p hp
        exact ⟨_, .inr ⟨p', hp', rfl⟩, (List.prefix_append_right_inj _).2 hpp', s₂,
          hrun.append hrun'⟩

theorem resR_mem_inf (ht : StoreDet t) (hr : (c, .ret b s₁) ∈ t.1 s a)
    {J : Set (List (Move E (sig1 A B)))} (hJ : J ∈ (threadT t s).inf)
    (hrJ : roundMoves (a, c, b) ∈ J) : resR (roundMoves (a, c, b)) J ∈ (threadT t s₁).inf := by
  obtain ⟨hJ, hsub, hk⟩ := hJ
  refine ⟨⟨?_, ?_, ?_⟩, fun p hp => (mem_after_round ht hr).1 (hsub hp), ?_⟩
  · intro p₀ p hp h
    exact hJ.of_prefix hp ((List.prefix_append_right_inj _).2 h)
  · intro p₁ p₂ h₁ h₂
    rcases hJ.total h₁ h₂ with h | h
    · exact .inl ((List.prefix_append_right_inj _).1 h)
    · exact .inr ((List.prefix_append_right_inj _).1 h)
  · intro k
    obtain ⟨q, hq, hk⟩ := hJ.unbounded (k + (roundMoves (a, c, b)).length)
    rcases hJ.total hrJ hq with ⟨p, rfl⟩ | h
    · exact ⟨p, hq, by simp at hk; omega⟩
    · have := h.length_le
      exact ⟨[], by simpa [resR] using hrJ, by omega⟩
  · rcases hk with ⟨pre, s₂, a', ω, hpre, hω, rfl⟩ | hk
    · obtain ⟨k, hk⟩ := hrJ
      have h₁ := prefix_pre_of_ans (u := .inr (.ask a) :: callMoves c) hk
      obtain ⟨pre', rfl⟩ := h₁
      refine .inl ⟨pre', s₂, a', ω, (round_det ht hr).1 hpre, hω, ?_⟩
      exact resR_streamPlay _ _ _ _
    · refine .inr fun p hp => ?_
      obtain ⟨q', hq', ⟨x, rfl⟩, s₂, hrun⟩ := hk _ hp
      refine ⟨p ++ x, by simpa [resR, List.append_assoc] using hq', List.prefix_append _ _, s₂, ?_⟩
      exact (round_det ht hr).1 (by simpa [List.append_assoc] using hrun)

end Residual

/-! ## The converse for store-deterministic triples -/

section Converse

variable {S' : Type u} {t : ObsTriple E S A B} {t' : ObsTriple E S' A B}

theorem inf_transfer (ht' : StoreDet t') {s : S} {s' : S'} {s₁ : S} {s₁' : S'} {a : A}
    {c : List (Call E)} {b : B} (hr : (c, .ret b s₁) ∈ t.1 s a)
    (hr' : (c, .ret b s₁') ∈ t'.1 s' a) (h : (threadT t s).inf = (threadT t' s').inf)
    {I : Set (List (Move E (sig1 A B)))} (hI : I ∈ (threadT t s₁).inf) :
    I ∈ (threadT t' s₁').inf := by
  have hJ := extR_mem_inf hr hI
  rw [h] at hJ
  have := resR_mem_inf ht' hr' hJ (.inl (List.prefix_refl _))
  rwa [resR_extR ((threadT t s₁).inf_isInf hI)] at this

theorem ret_match (ht : StoreDet t) (ht' : StoreDet t') {s : S} {s' : S'}
    (h : threadT t s = threadT t' s') {a : A} {c : List (Call E)} {b : B} {s₁ : S}
    (hr : (c, .ret b s₁) ∈ t.1 s a) :
    ∃ s₁', (c, .ret b s₁') ∈ t'.1 s' a ∧ threadT t s₁ = threadT t' s₁' := by
  have hm : roundMoves (a, c, b) ∈ (threadT t' s').toStrategy :=
    h ▸ mem_roundMoves.2 ⟨s₁, hr⟩
  obtain ⟨s₁', hr'⟩ := mem_roundMoves.1 hm
  refine ⟨s₁', hr', DStrategy.ext (Strategy.ext fun p => ?_) (Set.ext fun p => ?_) ?_⟩
  · rw [← mem_after_round ht hr, ← mem_after_round ht' hr', h]
  · rw [← div_after_round ht hr, ← div_after_round ht' hr', h]
  · exact (Set.Subset.antisymm (fun I hI => inf_transfer ht' hr hr' (congrArg DStrategy.inf h) hI)
      fun I hI => inf_transfer ht hr' hr (congrArg DStrategy.inf h.symm) hI)

theorem roundEq_of_eq (ht : StoreDet t) (ht' : StoreDet t') {s : S} {s' : S'}
    (h : threadT t s = threadT t' s') :
    RoundEq t t' (fun s s' => threadT t s = threadT t' s') s s' where
  trap a c := by
    have h₁ := mem_trap₁ (t := t) (s := s) (a := a) (c := c) (u := [])
    have h₂ := mem_trap₁ (t := t') (s := s') (a := a) (c := c) (u := [])
    rw [h] at h₁
    simpa using h₁.symm.trans h₂
  div a c := by
    have h₁ := mem_div₁ (t := t) (s := s) (a := a) (c := c)
    have h₂ := mem_div₁ (t := t') (s := s') (a := a) (c := c)
    rw [h] at h₁
    exact h₁.symm.trans h₂
  pend := by
    funext a
    ext ⟨c, m⟩
    have h₁ := mem_pending₁ (t := t) (s := s) (a := a) (c := c) (m := m)
    have h₂ := mem_pending₁ (t := t') (s := s') (a := a) (c := c) (m := m)
    rw [h] at h₁
    exact h₁.symm.trans h₂
  inf := by
    funext a
    ext ω
    have h₁ := mem_inf₁ (t := t) (s := s) (a := a) (ω := ω)
    have h₂ := mem_inf₁ (t := t') (s := s') (a := a) (ω := ω)
    rw [h] at h₁
    exact h₁.symm.trans h₂
  ret _ _ _ _ hr := ret_match ht ht' h hr
  ret' _ _ _ _ hr := by
    obtain ⟨s₁, h₁, h₂⟩ := ret_match ht' ht h.symm hr
    exact ⟨s₁, h₁, h₂.symm⟩

end Converse

/-! ## Pointwise agreement is not necessary -/

namespace Counter

variable {E : Sig.{0}}

/-- A function that keeps its store. -/
def keep : ObsTriple E Bool PUnit PUnit :=
  (fun s _ => {([], .ret () s)}, fun _ _ => ∅, fun _ _ => ∅)

/-- A function that flips its store. -/
def flip : ObsTriple E Bool PUnit PUnit :=
  (fun s _ => {([], .ret () (!s))}, fun _ _ => ∅, fun _ _ => ∅)

theorem satP_eq {f : AFun E Bool PUnit PUnit} (hf : ∀ s a c e, (c, e) ∈ f s a → c = [])
    (s : Bool) : satP ((f, fun _ _ => ∅, fun _ _ => ∅) : ObsTriple E Bool PUnit PUnit) s =
      fun _ => ∅ := by
  funext a
  ext ⟨c, m⟩
  refine ⟨?_, fun h => by simp at h⟩
  rintro (h | ⟨_, _, h, -⟩ | ⟨d, e, hd, n, c', rfl⟩ | ⟨_, h, -⟩)
  · simp at h
  · simp at h
  · simpa using hf s a _ e hd
  · simp at h

theorem isBisim : IsBisim (keep (E := E)) flip fun _ _ => True := fun s s' _ =>
  { trap := fun a c => by simp [keep, flip]
    div := fun a c => by simp [keep, flip]
    pend := by
      rw [keep, flip, satP_eq (by simp) s, satP_eq (by simp) s']
    inf := rfl
    ret := fun a c b s₁ h => ⟨!s', by simp_all [keep, flip], trivial⟩
    ret' := fun a c b s₁ h => ⟨s, by simp_all [keep, flip], trivial⟩ }

theorem not_pointwise :
    threadT (keep (E := E)) false = threadT flip false ∧
      ¬ ∀ s, Reach (keep (E := E)) false s → (keep (E := E)).1 s = flip.1 s := by
  refine ⟨threadT_eq_of_isBisim isBisim trivial, fun h => ?_⟩
  have := congrFun (h false (.refl _)) ()
  have hm : (([], .ret () false) : CallBeh E Bool PUnit) ∈ (keep (E := E)).1 false () := rfl
  rw [this] at hm
  simp [flip] at hm

end Counter

end Silmaril.Proofs.Games.Abstract.StratThread
