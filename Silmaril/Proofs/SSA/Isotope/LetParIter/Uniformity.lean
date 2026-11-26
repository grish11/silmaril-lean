module

public import Silmaril.SSA.Isotope.LetParIter.Thms

/-! # Transport of the native uniformity premise -/

public section

namespace Silmaril.Isotope.LetParIter.Proofs

open Parallel (Derivation)
open LetIter.LocallyNameless (HasType Pure)

universe u v w r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
  {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε]
  {pe : ε} {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A A' B : τ}
  {a : LetIter.LocallyNameless.Tm ν Φ n} {h b b' : LetIter.LocallyNameless.Tm ν Φ (n + 1)}

set_option backward.isDefEq.respectTransparency false in
theorem native_uniformity_of_aligned_square
    (align : ∀ {t : LetIter.LocallyNameless.Tm ν Φ (n + 1)}
      (d e : Derivation Φ Γ (.snoc β A) (embed t) (coprod B A')), Equiv pe Γ d e)
    (ha : HasType Φ Γ β a A) (hh : HasType Φ Γ (.snoc β A) h A') (hp : Pure pe h)
    (hb : HasType Φ Γ (.snoc β A) b (coprod B A))
    (hb' : HasType Φ Γ (.snoc β A') b' (coprod B A'))
    (square :
      ∃ (dl : Derivation Φ Γ (.snoc β A)
          (embed (.case b (.inl (.bv 0)) (.inr h.underBinder))) (coprod B A'))
        (dr : Derivation Φ Γ (.snoc β A)
          (embed (b'.underBinder.instantiate h)) (coprod B A')),
        Equiv pe Γ dl dr) :
    ∃ (dl : Derivation Φ Γ β (embed (.iter a b)) B)
      (dr : Derivation Φ Γ β (embed (.iter (.let₁ a h) b')) B), Equiv pe Γ dl dr := by
  let left := LetIter.LocallyNameless.Tm.case b (.inl (.bv 0)) (.inr h.underBinder)
  let right := b'.underBinder.instantiate h
  have hleft : embed left =
      Parallel.Tm.case hasCase (embed b) (.inl hasCase (.bv 0))
        (.inr hasCase (embed h).underBinder) := by
    simp only [left, embed, embed_underBinder]
  have hright : embed right = (embed b').underBinder.instantiate (embed h) := by
    simp only [right, embed_instantiate, embed_underBinder]
  have leftAligned := @align left
  have rightAligned := @align right
  change (∃ (dl : Derivation Φ Γ (.snoc β A) (embed left) (coprod B A'))
    (dr : Derivation Φ Γ (.snoc β A) (embed right) (coprod B A')), Equiv pe Γ dl dr) at square
  rw [hleft, hright] at square
  rw [hleft] at leftAligned
  rw [hright] at rightAligned
  obtain ⟨dl, dr, eq⟩ := square
  obtain ⟨da⟩ := LetIter.LocallyNameless.Derivation.ofHasType ha
  obtain ⟨dh⟩ := LetIter.LocallyNameless.Derivation.ofHasType hh
  obtain ⟨db⟩ := LetIter.LocallyNameless.Derivation.ofHasType hb
  obtain ⟨db'⟩ := LetIter.LocallyNameless.Derivation.ofHasType hb'
  refine ⟨derivation (.iter da db), derivation (.iter (.let₁ da dh) db'), ?_⟩
  exact .iterUniformity (derivation da) (derivation dh) (embed_pure hp)
    (derivation db) (derivation db') ((leftAligned _ dl).trans (eq.trans (rightAligned dr _)))

end Silmaril.Isotope.LetParIter.Proofs
