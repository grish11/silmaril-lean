module

public import Silmaril.Games.Abstract.SessionCat.Defs
public import Silmaril.Games.Abstract.StratOps.Thms

/-!
# Session-level category laws: sequencing and strength (proofs)

The laws of `seqS` are those of the Kleisli sequencing of the exception monad, derived from the
laws of `StratOps.seqT`, `caseT` and pure maps. The store strength `frameS` commutes with `seqT`,
`pureT`, `mapT` and `caseT`, componentwise.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionCat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps Silmaril.Games.Abstract.SessionCat

universe u

variable {E : Sig.{u}} {S S' A B C D : Type u}

/-! ## Sequencing -/

theorem seqS_retS (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) : seqS t retS = t := by
  rw [seqS, retS, trapS, caseT_pureT_mapT, seqT_pureT]

theorem retS_seqS (u : ObsTriple E S A (B ⊕ PUnit.{u + 1})) : seqS retS u = u :=
  pureT_mapT_inl_seqT_caseT _ _

theorem trapS_seqT_caseT (v : ObsTriple E S C (D ⊕ PUnit.{u + 1})) :
    seqT trapS (caseT v trapS) = (trapS : ObsTriple E S PUnit.{u + 1} (D ⊕ PUnit.{u + 1})) :=
  pureT_mapT_inr_seqT_caseT _ _

theorem seqS_assoc (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple E S B (C ⊕ PUnit.{u + 1})) (v : ObsTriple E S C (D ⊕ PUnit.{u + 1})) :
    seqS (seqS t u) v = seqS t (seqS u v) := by
  rw [seqS, seqS, seqT_assoc, seqT_caseT, trapS_seqT_caseT]
  rfl

theorem mem_seqS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {u : ObsTriple E S B (C ⊕ PUnit.{u + 1})}
    {s : S} {a : A} {x : List (Call E) × End S (C ⊕ PUnit.{u + 1})} :
    x ∈ (seqS t u).1 s a ↔ (∃ c, (c, End.trap) ∈ t.1 s a ∧ x = (c, End.trap)) ∨
      (∃ c, (c, End.div) ∈ t.1 s a ∧ x = (c, End.div)) ∨
      (∃ c s₁, (c, End.ret (.inr PUnit.unit) s₁) ∈ t.1 s a ∧
        x = (c, End.ret (.inr PUnit.unit) s₁)) ∨
      ∃ c₁ b s₁ c₂ e, (c₁, End.ret (.inl b) s₁) ∈ t.1 s a ∧ (c₂, e) ∈ u.1 s₁ b ∧
        x = (c₁ ++ c₂, e) := by
  constructor
  · rintro (h | h | ⟨c₁, b, s₁, c₂, e, hb, he, rfl⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · rcases b with b | ⟨⟩
      · exact .inr (.inr (.inr ⟨c₁, b, s₁, c₂, e, hb, he, rfl⟩))
      · obtain ⟨y, rfl, hy⟩ := he
        simp only [Prod.mk.injEq] at hy
        obtain ⟨rfl, rfl⟩ := hy
        exact .inr (.inr (.inl ⟨c₁, s₁, hb, by simp [FullFun.endMap]⟩))
  · rintro (h | h | ⟨c, s₁, h, rfl⟩ | ⟨c₁, b, s₁, c₂, e, hb, he, rfl⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨c, .inr PUnit.unit, s₁, [], _, h, ⟨_, rfl, rfl⟩,
        by simp [FullFun.endMap]⟩)
    · exact .inr (.inr ⟨c₁, .inl b, s₁, c₂, e, hb, he, rfl⟩)

/-! ## Store strength -/

theorem frameEnd_eq_ret {s' : S'} {e : End S B} {b : B} {σ : S × S'}
    (h : frameEnd s' e = End.ret b σ) : e = End.ret b σ.1 ∧ σ.2 = s' := by
  cases e with
  | ret b' s => simp only [frameEnd, End.ret.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | trap => cases h
  | div => cases h

theorem frameEnd_eq_trap {s' : S'} {e : End S B} (h : frameEnd s' e = End.trap) : e = End.trap := by
  cases e <;> first | rfl | cases h

theorem frameEnd_eq_div {s' : S'} {e : End S B} (h : frameEnd s' e = End.div) : e = End.div := by
  cases e <;> first | rfl | cases h

theorem frameS_seqT (t : ObsTriple E S A B) (u : ObsTriple E S B C) :
    frameS S' (seqT t u) = seqT (frameS S' t) (frameS S' u) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext σ a <;> ext x
  · constructor
    · rintro ⟨y, (⟨c, h, rfl⟩ | ⟨c, h, rfl⟩ | ⟨c₁, b, s₁, c₂, e, hb, he, rfl⟩), rfl⟩
      · exact .inl ⟨c, ⟨_, h, rfl⟩, rfl⟩
      · exact .inr (.inl ⟨c, ⟨_, h, rfl⟩, rfl⟩)
      · exact .inr (.inr ⟨c₁, b, (s₁, σ.2), c₂, frameEnd σ.2 e, ⟨_, hb, rfl⟩, ⟨_, he, rfl⟩, rfl⟩)
    · rintro (⟨c, ⟨y, h, hy⟩, rfl⟩ | ⟨c, ⟨y, h, hy⟩, rfl⟩ |
        ⟨c₁, b, σ₁, c₂, e, ⟨y, hb, hy⟩, ⟨z, he, hz⟩, rfl⟩)
      · obtain ⟨rfl, hy⟩ := Prod.ext_iff.1 hy
        exact ⟨_, .inl ⟨_, by rwa [← frameEnd_eq_trap hy], rfl⟩, rfl⟩
      · obtain ⟨rfl, hy⟩ := Prod.ext_iff.1 hy
        exact ⟨_, .inr (.inl ⟨_, by rwa [← frameEnd_eq_div hy], rfl⟩), rfl⟩
      · obtain ⟨rfl, hy⟩ := Prod.ext_iff.1 hy
        obtain ⟨hy, hσ⟩ := frameEnd_eq_ret hy
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hz
        refine ⟨(y.1 ++ z.1, z.2), .inr (.inr ⟨y.1, b, σ₁.1, z.1, z.2, hy ▸ hb, he, rfl⟩), ?_⟩
        simp [hσ]
  · constructor
    · rintro (h | ⟨c₁, b, s₁, c₂, m, hb, hm, rfl⟩)
      · exact .inl h
      · exact .inr ⟨c₁, b, (s₁, σ.2), c₂, m, ⟨_, hb, rfl⟩, hm, rfl⟩
    · rintro (h | ⟨c₁, b, σ₁, c₂, m, ⟨y, hb, hy⟩, hm, rfl⟩)
      · exact .inl h
      · obtain ⟨rfl, hy⟩ := Prod.ext_iff.1 hy
        obtain ⟨hy, -⟩ := frameEnd_eq_ret hy
        exact .inr ⟨y.1, b, σ₁.1, c₂, m, hy ▸ hb, hm, rfl⟩
  · constructor
    · rintro (h | ⟨c, b, s₁, ω', hb, hω, rfl⟩)
      · exact .inl h
      · exact .inr ⟨c, b, (s₁, σ.2), ω', ⟨_, hb, rfl⟩, hω, rfl⟩
    · rintro (h | ⟨c, b, σ₁, ω', ⟨y, hb, hy⟩, hω, rfl⟩)
      · exact .inl h
      · obtain ⟨rfl, hy⟩ := Prod.ext_iff.1 hy
        obtain ⟨hy, -⟩ := frameEnd_eq_ret hy
        exact .inr ⟨y.1, b, σ₁.1, ω', hy ▸ hb, hω, rfl⟩

theorem frameS_pureT : frameS S' (pureT : ObsTriple E S A A) = pureT := by
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  funext σ a
  simp [frameS, pureT, ofFull, FullFun.pure, frameEnd]

theorem frameS_mapT (t : ObsTriple E S A B) (h : B → C) :
    frameS S' (mapT t h) = mapT (frameS S' t) h := by
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  funext σ a
  simp only [frameS, mapT, ofFull, full, FullFun.map, Set.image_image]
  congr 1
  funext x
  rcases x with ⟨c, _ | _ | _⟩ <;> rfl

theorem frameS_caseT (t : ObsTriple E S A C) (u : ObsTriple E S B C) :
    frameS S' (caseT t u) = caseT (frameS S' t) (frameS S' u) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext σ x <;> rcases x with a | a <;> rfl

theorem frameS_retS : frameS S' (retS : ObsTriple E S A (A ⊕ PUnit.{u + 1})) = retS := by
  rw [retS, frameS_mapT, frameS_pureT]
  rfl

theorem frameS_seqS (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple E S B (C ⊕ PUnit.{u + 1})) :
    frameS S' (seqS t u) = seqS (frameS S' t) (frameS S' u) := by
  rw [seqS, seqS, frameS_seqT, frameS_caseT, trapS, frameS_mapT, frameS_pureT]
  rfl

end Silmaril.Proofs.Games.Abstract.SessionCat
