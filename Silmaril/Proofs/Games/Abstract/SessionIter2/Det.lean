module

public import Silmaril.Games.Abstract.SessionIter2.Defs
public import Silmaril.Games.Abstract.SessionCat.Thms

/-!
# Session sequencing preserves determinism given answers (proofs)

Two behaviours of `seqS t u` each start with a behaviour of `t` (a plain trap, a divergence, a
continuing trap, or a value followed by a behaviour of `u`). `AFun.Det t.1` makes the two
`t`-parts agree; when their ends coincide, they are both values `b` at the same store, and
`AFun.Det u.1` makes the `u`-parts agree (`agree_append`). Nothing is hidden by sequencing, so
unlike linking (`SessionLinkCex.not_det_linkS_may`) a return and a divergence with the same log
cannot arise.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionIter2

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.SessionCat

universe u

variable {E : Sig.{u}}

/-- Agreement of the first parts, and of the rest when the first parts end alike, give agreement
of the concatenations. -/
theorem agree_append {S₀ B₀ S₁ B₁ : Type u} {c c' L L' : List (Call E)} {e₀ e₀' : End S₀ B₀}
    {e e' : End S₁ B₁} (h : AFun.Agree c e₀ c' e₀') (hk : e₀ = e₀' → AFun.Agree L e L' e') :
    AFun.Agree (c ++ L) e (c' ++ L') e' := by
  induction c generalizing c' with
  | nil =>
    cases c' with
    | nil => exact hk h
    | cons x c' => obtain ⟨m, n⟩ := x; exact h.elim
  | cons x c ih =>
    cases c' with
    | nil => obtain ⟨m, n⟩ := x; exact h.elim
    | cons x' c' =>
      obtain ⟨m, n⟩ := x
      obtain ⟨m', n'⟩ := x'
      exact ⟨h.1, fun hn => ih (h.2 hn)⟩

/-- Agreement transported along ends that are equal when the original ends are. -/
theorem agree_of_agree {S₀ B₀ S₁ B₁ : Type u} {c c' : List (Call E)} {e₀ e₀' : End S₀ B₀}
    {e e' : End S₁ B₁} (h : AFun.Agree c e₀ c' e₀') (hk : e₀ = e₀' → e = e') :
    AFun.Agree c e c' e' := by
  simpa using agree_append (L := []) (L' := []) h hk

variable {S A B C : Type u}

/-- **Session sequencing preserves determinism given answers.** -/
theorem det_seqS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    {u : ObsTriple E S B (C ⊕ PUnit.{u + 1})} (ht : AFun.Det t.1) (hu : AFun.Det u.1) :
    AFun.Det (seqS t u).1 := by
  intro s a x y hx hy
  rcases SessionCat.mem_seqS.1 hx with ⟨c, h, rfl⟩ | ⟨c, h, rfl⟩ | ⟨c, s₁, h, rfl⟩ |
      ⟨c₁, b, s₁, c₂, e, h, he, rfl⟩ <;>
    rcases SessionCat.mem_seqS.1 hy with ⟨c', h', rfl⟩ | ⟨c', h', rfl⟩ | ⟨c', s₁', h', rfl⟩ |
      ⟨c₁', b', s₁', c₂', e', h', he', rfl⟩
  all_goals first
    | exact agree_of_agree (ht _ _ _ _ h h') fun h => by cases h; rfl
    | exact agree_of_agree (ht _ _ _ _ h h') fun h => by cases h
    | simpa using agree_append (L := []) (ht _ _ _ _ h h') fun h => by cases h
    | simpa using agree_append (L' := []) (ht _ _ _ _ h h') fun h => by cases h
    | exact agree_append (ht _ _ _ _ h h') fun h => by
        simp only [End.ret.injEq, Sum.inl.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hu _ _ _ _ he he'

end Silmaril.Proofs.Games.Abstract.SessionIter2
