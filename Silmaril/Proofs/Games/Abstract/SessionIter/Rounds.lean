module

public import Silmaril.Games.Abstract.SessionIter.Defs
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Proofs.Games.Abstract.SessionIter.Det

/-!
# Session iteration: rounds of the session strategies (proofs)

The completed rounds of a triple only see its returns, so the rounds of `seqS t u` and
`iterS t` are `RoundsBy` the one-round relations `SeqRet t u` and `IterRet t`
(`mem_seqS_ret`, `mem_iterS_ret`). The session of a framed triple is the session of the triple:
the untouched store component is carried by a bisimulation.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionIter

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps Silmaril.Games.Abstract.StratThread
  Silmaril.Games.Abstract.StratSession Silmaril.Games.Abstract.SessionCat
  Silmaril.Games.Abstract.SessionIter

universe u

variable {E : Sig.{u}} {S A B C : Type u}

theorem roundsBy_congr {R R' : S → A → List (Call E) → B → S → Prop}
    (h : ∀ s a c b s', R s a c b s' ↔ R' s a c b s') {s s' : S}
    {rs : List (A × List (Call E) × B)} : RoundsBy R s rs s' ↔ RoundsBy R' s rs s' := by
  constructor
  · intro hr
    induction hr with
    | nil => exact .nil _
    | cons h₁ _ ih => exact .cons ((h _ _ _ _ _).1 h₁) ih
  · intro hr
    induction hr with
    | nil => exact .nil _
    | cons h₁ _ ih => exact .cons ((h _ _ _ _ _).2 h₁) ih

theorem rounds_iff_roundsBy {t : ObsTriple E S A B} {s s' : S}
    {rs : List (A × List (Call E) × B)} :
    Rounds t s rs s' ↔ RoundsBy (fun s a c b s' => (c, End.ret b s') ∈ t.1 s a) s rs s' := by
  constructor
  · intro hr
    induction hr with
    | nil => exact .nil _
    | cons h₁ _ ih => exact .cons h₁ ih
  · intro hr
    induction hr with
    | nil => exact .nil _
    | cons h₁ _ ih => exact .cons h₁ ih

theorem rounds_seqS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    {u : ObsTriple E S B (C ⊕ PUnit.{u + 1})} {s s' : S}
    {rs : List (A × List (Call E) × (C ⊕ PUnit.{u + 1}))} :
    Rounds (seqS t u) s rs s' ↔ RoundsBy (SeqRet t u) s rs s' :=
  rounds_iff_roundsBy.trans (roundsBy_congr fun _ _ _ _ _ => mem_seqS_ret)

theorem rounds_iterS {t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})} {s s' : S}
    {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} :
    Rounds (iterS t) s rs s' ↔ RoundsBy (IterRet t) s rs s' :=
  rounds_iff_roundsBy.trans (roundsBy_congr fun _ _ _ _ _ => mem_iterS_ret)

theorem trap_mem_seqS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    {u : ObsTriple E S B (C ⊕ PUnit.{u + 1})} {s : S} {a : A} {c : List (Call E)} :
    (c, End.trap) ∈ (seqS t u).1 s a ↔ (c, End.trap) ∈ t.1 s a ∨
      ∃ c₁ b s₁ c₂, (c₁, End.ret (.inl b) s₁) ∈ t.1 s a ∧ (c₂, End.trap) ∈ u.1 s₁ b ∧
        c = c₁ ++ c₂ := by
  rw [SessionCat.mem_seqS]
  constructor
  · rintro (⟨c', h, hx⟩ | ⟨_, _, hx⟩ | ⟨_, _, _, hx⟩ | ⟨c₁, b, s₁, c₂, e, h₁, he, hx⟩)
    · cases hx; exact .inl h
    · cases hx
    · cases hx
    · simp only [Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact .inr ⟨c₁, b, s₁, c₂, h₁, he, rfl⟩
  · rintro (h | ⟨c₁, b, s₁, c₂, h₁, he, rfl⟩)
    · exact .inl ⟨c, h, rfl⟩
    · exact .inr (.inr (.inr ⟨c₁, b, s₁, c₂, _, h₁, he, rfl⟩))

theorem sroundsMoves_singleton (r : A × List (Call E) × (B ⊕ PUnit.{u + 1})) :
    sroundsMoves [r] = sroundMoves r := by
  simp [sroundsMoves]

theorem roundsBy_singleton {R : S → A → List (Call E) → B → S → Prop} {s s' : S} {a : A}
    {c : List (Call E)} {b : B} : RoundsBy R s [(a, c, b)] s' ↔ R s a c b s' := by
  constructor
  · rintro (_ | ⟨h, (_ | _)⟩)
    exact h
  · exact fun h => .cons h (.nil _)

/-- **One session round of a sequence**, without plain traps. -/
theorem mem_sroundMoves_seqS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    {u : ObsTriple E S B (C ⊕ PUnit.{u + 1})} (ht : NoPlainTrap t) (hu : NoPlainTrap u)
    {s₀ : S} {a : A} {c : List (Call E)} {x : C ⊕ PUnit.{u + 1}} :
    sroundMoves (a, c, x) ∈ (threadS (seqS t u) s₀).toStrategy ↔ ∃ s, SeqRet t u s₀ a c x s := by
  rw [← sroundsMoves_singleton, mem_srounds_of_noPlainTrap (noPlainTrap_seqS ht hu)]
  simp only [rounds_seqS, roundsBy_singleton]

/-- **One session round of an iteration**, without plain traps. -/
theorem mem_sroundMoves_iterS {t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})}
    (ht : NoPlainTrap t) {s₀ : S} {a : A} {c : List (Call E)} {x : B ⊕ PUnit.{u + 1}} :
    sroundMoves (a, c, x) ∈ (threadS (iterS t) s₀).toStrategy ↔ ∃ s, IterRet t s₀ a c x s := by
  rw [← sroundsMoves_singleton, mem_srounds_of_noPlainTrap (noPlainTrap_iterS ht)]
  simp only [rounds_iterS, roundsBy_singleton]

/-! ## Strength -/

theorem frameEnd_eq_ret' {S' : Type u} {s' : S'} {e : End S B} {b : B} {σ : S × S'}
    (h : frameEnd s' e = End.ret b σ) : e = End.ret b σ.1 ∧ σ.2 = s' := by
  cases e with
  | ret b' s => simp only [frameEnd, End.ret.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | trap => cases h
  | div => cases h

theorem frameEnd_eq_trap' {S' : Type u} {s' : S'} {e : End S B} (h : frameEnd s' e = End.trap) :
    e = End.trap := by
  cases e <;> first | rfl | cases h

theorem frameEnd_eq_div' {S' : Type u} {s' : S'} {e : End S B} (h : frameEnd s' e = End.div) :
    e = End.div := by
  cases e <;> first | rfl | cases h

theorem satP_frameS {S' D : Type u} (t : ObsTriple E S A D) (σ : S × S') :
    satP (frameS S' t) σ = satP t σ.1 := by
  funext a
  ext x
  simp only [satP, frameS, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro (h | h | ⟨d, e, ⟨y, hy, hye⟩, hd⟩ | h)
    · exact .inl h
    · exact .inr (.inl h)
    · obtain ⟨rfl, -⟩ := Prod.mk.inj hye
      exact .inr (.inr (.inl ⟨_, _, hy, hd⟩))
    · exact .inr (.inr (.inr h))
  · rintro (h | h | ⟨d, e, hy, hd⟩ | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl ⟨d, _, ⟨_, hy, rfl⟩, hd⟩))
    · exact .inr (.inr (.inr h))

theorem isBisim_frameS {S' D : Type u} (t : ObsTriple E S A D) (s' : S') :
    IsBisim (frameS S' t) t fun σ s₀ => σ = (s₀, s') := by
  rintro σ s₀ rfl
  refine ⟨fun a c => ⟨?_, ?_⟩, fun a c => ⟨?_, ?_⟩, satP_frameS t _, rfl, ?_, ?_⟩
  · rintro ⟨y, hy, hye⟩
    obtain ⟨rfl, he⟩ := Prod.mk.inj hye
    rwa [← frameEnd_eq_trap' he]
  · exact fun h => ⟨_, h, rfl⟩
  · rintro ⟨y, hy, hye⟩
    obtain ⟨rfl, he⟩ := Prod.mk.inj hye
    rwa [← frameEnd_eq_div' he]
  · exact fun h => ⟨_, h, rfl⟩
  · rintro a c b σ₁ ⟨y, hy, hye⟩
    obtain ⟨rfl, he⟩ := Prod.mk.inj hye
    obtain ⟨he, hσ⟩ := frameEnd_eq_ret' he
    exact ⟨σ₁.1, he ▸ hy, Prod.ext rfl hσ⟩
  · intro a c b s₁ h
    exact ⟨(s₁, s'), ⟨_, h, rfl⟩, rfl⟩

theorem threadS_frameS {S' : Type u} (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) (s : S) (s' : S') :
    threadS (frameS S' t) (s, s') = threadS t s :=
  threadS_eq_of_obsEq ⟨_, isBisim_frameS t s', rfl⟩

end Silmaril.Proofs.Games.Abstract.SessionIter
