module

public import Silmaril.SSA.Isotope.LetParIter.Thms
import Silmaril.Proofs.SSA.Isotope.LetParIter.Uniformity

/-! # Transport of the native uniformity premise -/

public section

namespace Silmaril.Isotope.LetParIter

open Parallel (Derivation)
open LetIter.LocallyNameless (HasType Pure)

universe u v w r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
  {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε]
  {pe : ε} {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A A' B : τ}
  {a : LetIter.LocallyNameless.Tm ν Φ n} {h b b' : LetIter.LocallyNameless.Tm ν Φ (n + 1)}

/-- The native recursive uniformity step lifts from a witnessed square when
the square's native typing fibers are aligned. -/
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
      (dr : Derivation Φ Γ β (embed (.iter (.let₁ a h) b')) B), Equiv pe Γ dl dr :=
  Proofs.native_uniformity_of_aligned_square align ha hh hp hb hb' square

end Silmaril.Isotope.LetParIter
