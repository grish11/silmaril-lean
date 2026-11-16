module

public import Silmaril.Games.Abstract.SessionPair.Defs
public import Silmaril.Games.Abstract.StratThread.Thms
public import Silmaril.Games.DPair.Defs
import Silmaril.Proofs.Games.Abstract.SessionPair.Basic

/-!
# Pairing sessions: the automata

* **Sessions without plain traps.** A play of `threadS t s₀` is a play `p` whose answers, read as
  returns (`unmerge`), are a play of `threadT t s₀` (`mem_threadS_iff`, `mem_div_threadS_iff`).
* **Related states** (`PRel`): the paired automaton is idle at `(s₁, s₂)` when both components
  are idle at `s₁` and `s₂`; it runs or waits on `.inl a` when the left component does, at the
  same calls, while the right one is idle at the second store; symmetrically on the right.
* **Simulation** in both directions along the halves of a play (`fwd`, `bwd`), one move at a time
  (`fstep`, `bstep`), with the positions of the pairing game (`posOf`, `pos_step`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionPair

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratThread
open Silmaril.Games.Abstract.StratSession
open Silmaril.Games.Abstract.StratObs (callMoves satP)

universe u

variable {E : Sig.{u}}

/-! ## Sessions without plain traps -/

section Unmerge

variable {S A B : Type u}

/-- Read every answer as a return. -/
def unmerge : Move E (sig1 A B) → Move E (sig1 A (B ⊕ PUnit.{u + 1}))
  | .inl e => .inl e
  | .inr (.ask a) => .inr (.ask a)
  | .inr (.ans a x) => .inr (.ans a (.inl x))

theorem relMove_unmerge (o : Move E (sig1 A B)) : relMove (unmerge o) = o := by
  rcases o with e | (a | ⟨a, x⟩) <;> rfl

theorem map_relMove_unmerge (p : List (Move E (sig1 A B))) : (p.map unmerge).map relMove = p := by
  simp [List.map_map, Function.comp_def, relMove_unmerge]

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {s₀ : S}

theorem map_unmerge_relMove (ht : NoPlainTrap t) {x y : TSt E S A}
    {p : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))} (h : TRun t.1 (satP t) x p y) :
    (p.map relMove).map unmerge = p := by
  induction h with
  | nil => rfl
  | cons hs _ ih =>
    cases hs with
    | trap _ _ _ hr => exact absurd hr (ht _ _ _)
    | _ => simp only [List.map_cons, ih]; rfl

theorem mem_threadS_iff (ht : NoPlainTrap t) {p : List (Move E (sig1 A B))} :
    p ∈ (threadS t s₀).toStrategy ↔ p.map unmerge ∈ (threadT t s₀).toStrategy := by
  constructor
  · rintro ⟨p', ⟨y, hp'⟩, rfl⟩
    rw [map_unmerge_relMove ht hp']
    exact ⟨y, hp'⟩
  · intro h
    exact ⟨_, h, map_relMove_unmerge p⟩

theorem mem_div_threadS_iff (ht : NoPlainTrap t) {p : List (Move E (sig1 A B))} :
    p ∈ (threadS t s₀).div ↔ p.map unmerge ∈ (threadT t s₀).div := by
  constructor
  · rintro ⟨p', hp', rfl⟩
    obtain ⟨_, _, _, hr, _⟩ := id hp'
    rw [map_unmerge_relMove ht hr]
    exact hp'
  · intro h
    exact ⟨_, h, map_relMove_unmerge p⟩

end Unmerge

/-! ## Related states -/

section Pair

variable {S₁ S₂ A₁ A₂ B₁ B₂ : Type u}
  {t₁ : ObsTriple E S₁ A₁ (B₁ ⊕ PUnit.{u + 1})} {t₂ : ObsTriple E S₂ A₂ (B₂ ⊕ PUnit.{u + 1})}

/-- Related states of the paired automaton and of the two component automata, with the current
side. -/
inductive PRel : TSt E (S₁ × S₂) (A₁ ⊕ A₂) → Bool → TSt E S₁ A₁ → TSt E S₂ A₂ → Prop
  | idle (s₁ : S₁) (s₂ : S₂) (b : Bool) : PRel (.idle (s₁, s₂)) b (.idle s₁) (.idle s₂)
  | runL (s₁ : S₁) (s₂ : S₂) (a : A₁) (c : List (Call E)) :
      PRel (.run (s₁, s₂) (.inl a) c) false (.run s₁ a c) (.idle s₂)
  | waitL (s₁ : S₁) (s₂ : S₂) (a : A₁) (c : List (Call E)) (m : E.Op) :
      PRel (.wait (s₁, s₂) (.inl a) c m) false (.wait s₁ a c m) (.idle s₂)
  | runR (s₁ : S₁) (s₂ : S₂) (a : A₂) (c : List (Call E)) :
      PRel (.run (s₁, s₂) (.inr a) c) true (.idle s₁) (.run s₂ a c)
  | waitR (s₁ : S₁) (s₂ : S₂) (a : A₂) (c : List (Call E)) (m : E.Op) :
      PRel (.wait (s₁, s₂) (.inr a) c m) true (.idle s₁) (.wait s₂ a c m)

/-- The position of the pairing game of a paired automaton state. -/
def posOf : TSt E (S₁ × S₂) (A₁ ⊕ A₂) → Pos E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)
  | .idle _ => .idle
  | .run _ a _ => .run a
  | .wait _ a _ m => .wait a m
  | .dead => .idle
  | .stuck a => .run a

/-- The raw move of the paired automaton for a move of the pairing. -/
abbrev pm (o : Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)) :
    Move E (sig1 (A₁ ⊕ A₂) ((B₁ ⊕ B₂) ⊕ PUnit.{u + 1})) :=
  unmerge (pairMove o)

theorem halves_cons (b : Bool) (o : Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))
    (q : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))) :
    Split.halves b (o :: q) =
      ((Split.halves b [o]).1 ++ (Split.halves (Split.side b [o]) q).1,
        (Split.halves b [o]).2 ++ (Split.halves (Split.side b [o]) q).2) ∧
    Split.side b (o :: q) = Split.side (Split.side b [o]) q := by
  rcases o with e | (a | ⟨a, r⟩)
  · cases b <;> exact ⟨rfl, rfl⟩
  · rcases a with a | a <;> exact ⟨rfl, rfl⟩
  · rcases a with a | a <;> exact ⟨rfl, rfl⟩

theorem pos_step {x x' : TSt E (S₁ × S₂) (A₁ ⊕ A₂)} {o : Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)}
    (h : TStep (pairS t₁ t₂).1 (satP (pairS t₁ t₂)) x (pm o) x') :
    Step (posOf x) o (posOf x') := by
  rcases o with (m | ⟨m, n⟩) | (a | ⟨a | a, r⟩) <;> cases h <;> constructor

/-- One move of the paired automaton is a move of the component of its side. -/
theorem fstep {x x' : TSt E (S₁ × S₂) (A₁ ⊕ A₂)} {o : Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)}
    {b : Bool} {x₁ : TSt E S₁ A₁} {x₂ : TSt E S₂ A₂}
    (h : TStep (pairS t₁ t₂).1 (satP (pairS t₁ t₂)) x (pm o) x') (hr : PRel x b x₁ x₂) :
    ∃ x₁' x₂', TRun t₁.1 (satP t₁) x₁ ((Split.halves b [o]).1.map unmerge) x₁' ∧
      TRun t₂.1 (satP t₂) x₂ ((Split.halves b [o]).2.map unmerge) x₂' ∧
      PRel x' (Split.side b [o]) x₁' x₂' := by
  rcases o with (m | ⟨m, n⟩) | (a | ⟨a | a, r⟩)
  · cases h with
    | call σ a c m hp =>
      cases hr with
      | runL s₁ s₂ a c =>
        rw [satP_pairS_inl] at hp
        exact ⟨_, _, .cons (.call _ _ _ _ hp) (.nil _), .nil _, .waitL _ _ _ _ _⟩
      | runR s₁ s₂ a c =>
        rw [satP_pairS_inr] at hp
        exact ⟨_, _, .nil _, .cons (.call _ _ _ _ hp) (.nil _), .waitR _ _ _ _ _⟩
  · cases h with
    | reply σ a c m n =>
      cases hr with
      | waitL s₁ s₂ a c m =>
        exact ⟨_, _, .cons (.reply _ _ _ _ n) (.nil _), .nil _, .runL _ _ _ _⟩
      | waitR s₁ s₂ a c m =>
        exact ⟨_, _, .nil _, .cons (.reply _ _ _ _ n) (.nil _), .runR _ _ _ _⟩
  · rcases a with a | a
    · cases h with
      | ask σ a =>
        cases hr with
        | idle s₁ s₂ b => exact ⟨_, _, .cons (.ask _ a) (.nil _), .nil _, .runL _ _ _ _⟩
      | deadAsk a => cases hr
    · cases h with
      | ask σ a =>
        cases hr with
        | idle s₁ s₂ b => exact ⟨_, _, .nil _, .cons (.ask _ a) (.nil _), .runR _ _ _ _⟩
      | deadAsk a => cases hr
  · cases h with
    | ret σ a c x σ' hx =>
      cases hr with
      | runL s₁ s₂ a c =>
        obtain ⟨e, he, hx⟩ := mem_pairS_inl.1 hx
        cases e with
        | ret y s =>
          simp only [endL, End.ret.injEq] at hx
          obtain ⟨hy, rfl⟩ := hx
          cases Sum.map_injective.2 ⟨Sum.inl_injective, Function.injective_id⟩ hy
          exact ⟨_, _, .cons (.ret _ _ _ _ _ he) (.nil _), .nil _, .idle _ _ _⟩
        | trap => simp [endL] at hx
        | div => simp [endL] at hx
  · cases h with
    | ret σ a c x σ' hx =>
      cases hr with
      | runR s₁ s₂ a c =>
        obtain ⟨e, he, hx⟩ := mem_pairS_inr.1 hx
        cases e with
        | ret y s =>
          simp only [endR, End.ret.injEq] at hx
          obtain ⟨hy, rfl⟩ := hx
          cases Sum.map_injective.2 ⟨Sum.inr_injective, Function.injective_id⟩ hy
          exact ⟨_, _, .nil _, .cons (.ret _ _ _ _ _ he) (.nil _), .idle _ _ _⟩
        | trap => simp [endR] at hx
        | div => simp [endR] at hx

/-- One move of a component on its side is a move of the paired automaton, if the move is legal
in the pairing game. -/
theorem bstep {x : TSt E (S₁ × S₂) (A₁ ⊕ A₂)} {o : Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)}
    {b : Bool} {x₁ x₁' : TSt E S₁ A₁} {x₂ x₂' : TSt E S₂ A₂} {g : Pos E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)}
    (h₁ : TRun t₁.1 (satP t₁) x₁ ((Split.halves b [o]).1.map unmerge) x₁')
    (h₂ : TRun t₂.1 (satP t₂) x₂ ((Split.halves b [o]).2.map unmerge) x₂')
    (hr : PRel x b x₁ x₂) (hg : Step (posOf x) o g) :
    ∃ x', TStep (pairS t₁ t₂).1 (satP (pairS t₁ t₂)) x (pm o) x' ∧
      PRel x' (Split.side b [o]) x₁' x₂' := by
  rcases o with (m | ⟨m, n⟩) | (a | ⟨a | a, r⟩)
  · cases b
    · cases h₂
      cases h₁ with
      | cons hs hn =>
        cases hn
        cases hs with
        | call s a c m hp =>
          cases hr with
          | runL s₁ s₂ a c =>
            rw [← satP_pairS_inl (t₂ := t₂) (σ := (s, s₂))] at hp
            exact ⟨_, .call _ _ _ _ hp, .waitL _ _ _ _ _⟩
    · cases h₁
      cases h₂ with
      | cons hs hn =>
        cases hn
        cases hs with
        | call s a c m hp =>
          cases hr with
          | runR s₁ s₂ a c =>
            rw [← satP_pairS_inr (t₁ := t₁) (σ := (s₁, s))] at hp
            exact ⟨_, .call _ _ _ _ hp, .waitR _ _ _ _ _⟩
  · cases b
    · cases h₂
      cases h₁ with
      | cons hs hn =>
        cases hn
        cases hs with
        | reply s a c m n =>
          cases hr with
          | waitL s₁ s₂ a c m => exact ⟨_, .reply _ _ _ _ n, .runL _ _ _ _⟩
    · cases h₁
      cases h₂ with
      | cons hs hn =>
        cases hn
        cases hs with
        | reply s a c m n =>
          cases hr with
          | waitR s₁ s₂ a c m => exact ⟨_, .reply _ _ _ _ n, .runR _ _ _ _⟩
  · rcases a with a | a
    · cases h₂
      cases h₁ with
      | cons hs hn =>
        cases hn
        cases hs with
        | ask s a =>
          cases hr with
          | idle s₁ s₂ b => exact ⟨_, .ask _ _, .runL _ _ _ _⟩
          | runR => cases hg
          | waitR => cases hg
        | deadAsk a => cases hr
    · cases h₁
      cases h₂ with
      | cons hs hn =>
        cases hn
        cases hs with
        | ask s a =>
          cases hr with
          | idle s₁ s₂ b => exact ⟨_, .ask _ _, .runR _ _ _ _⟩
          | runL => cases hg
          | waitL => cases hg
        | deadAsk a => cases hr
  · cases h₂
    cases h₁ with
    | cons hs hn =>
      cases hn
      cases hs with
      | ret s a c y s' hy =>
        cases hr with
        | runL s₁ s₂ a c =>
          exact ⟨_, .ret _ _ _ _ _ (mem_pairS_inl.2 ⟨_, hy, rfl⟩), .idle _ _ _⟩
  · cases h₁
    cases h₂ with
    | cons hs hn =>
      cases hn
      cases hs with
      | ret s a c y s' hy =>
        cases hr with
        | runR s₁ s₂ a c =>
          exact ⟨_, .ret _ _ _ _ _ (mem_pairS_inr.2 ⟨_, hy, rfl⟩), .idle _ _ _⟩

/-- **Forward simulation**: a run of the paired automaton splits into runs of the components on
the halves. -/
theorem fwd {q : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))} :
    ∀ {x y : TSt E (S₁ × S₂) (A₁ ⊕ A₂)} {b : Bool} {x₁ : TSt E S₁ A₁} {x₂ : TSt E S₂ A₂},
      TRun (pairS t₁ t₂).1 (satP (pairS t₁ t₂)) x (q.map pm) y → PRel x b x₁ x₂ →
      ∃ y₁ y₂, TRun t₁.1 (satP t₁) x₁ ((Split.halves b q).1.map unmerge) y₁ ∧
        TRun t₂.1 (satP t₂) x₂ ((Split.halves b q).2.map unmerge) y₂ ∧
        PRel y (Split.side b q) y₁ y₂ := by
  induction q with
  | nil =>
    intro x y b x₁ x₂ h hr
    cases h
    exact ⟨x₁, x₂, .nil _, .nil _, hr⟩
  | cons o q ih =>
    intro x y b x₁ x₂ h hr
    cases h with
    | cons hs hq =>
      obtain ⟨x₁', x₂', h₁, h₂, hr'⟩ := fstep hs hr
      obtain ⟨y₁, y₂, k₁, k₂, hr''⟩ := ih hq hr'
      obtain ⟨e, e'⟩ := halves_cons b o q
      rw [e, e']
      exact ⟨y₁, y₂, by rw [List.map_append]; exact h₁.append k₁,
        by rw [List.map_append]; exact h₂.append k₂, hr''⟩

/-- **Backward simulation**: runs of the components on the halves of a legal play combine into a
run of the paired automaton. -/
theorem bwd {q : List (Move E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂))} :
    ∀ {x : TSt E (S₁ × S₂) (A₁ ⊕ A₂)} {b : Bool} {x₁ y₁ : TSt E S₁ A₁} {x₂ y₂ : TSt E S₂ A₂}
      {g : Pos E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)},
      TRun t₁.1 (satP t₁) x₁ ((Split.halves b q).1.map unmerge) y₁ →
      TRun t₂.1 (satP t₂) x₂ ((Split.halves b q).2.map unmerge) y₂ →
      PRel x b x₁ x₂ → Path (posOf x) q g →
      ∃ y, TRun (pairS t₁ t₂).1 (satP (pairS t₁ t₂)) x (q.map pm) y ∧
        PRel y (Split.side b q) y₁ y₂ := by
  induction q with
  | nil =>
    intro x b x₁ y₁ x₂ y₂ g h₁ h₂ hr _
    cases h₁
    cases h₂
    exact ⟨x, .nil _, hr⟩
  | cons o q ih =>
    intro x b x₁ y₁ x₂ y₂ g h₁ h₂ hr hg
    obtain ⟨e, e'⟩ := halves_cons b o q
    rw [e, List.map_append] at h₁ h₂
    rw [e']
    obtain ⟨x₁', k₁, l₁⟩ := h₁.of_append
    obtain ⟨x₂', k₂, l₂⟩ := h₂.of_append
    cases hg with
    | cons hs hg =>
      obtain ⟨x', hx', hr'⟩ := bstep k₁ k₂ hr hs
      cases Step.det hs (pos_step hx')
      obtain ⟨y, hy, hr''⟩ := ih l₁ l₂ hr' hg
      exact ⟨y, .cons hx' hy, hr''⟩

end Pair

end Silmaril.Proofs.Games.Abstract.SessionPair
