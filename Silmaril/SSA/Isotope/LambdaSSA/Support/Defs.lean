module

public import Silmaril.SSA.Isotope.LambdaSSA.Defs

/-! # Free value-variable occurrences in positional expressions -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Tm

universe u
variable {Φ : Type u}

/-- A free variable occurrence, accounting for every local binder. -/
def UsesVar : Tm Φ → Nat → Prop
  | .var j, i => i = j
  | .op _ x, i | .inl x, i | .inr x, i | .abort x, i => x.UsesVar i
  | .let₁ x body, i => x.UsesVar i ∨ body.UsesVar (i + 1)
  | .pair x y, i => x.UsesVar i ∨ y.UsesVar i
  | .unit, _ => False
  | .let₂ x body, i => x.UsesVar i ∨ body.UsesVar (i + 2)
  | .case x left right, i => x.UsesVar i ∨ left.UsesVar (i + 1) ∨ right.UsesVar (i + 1)

instance usesVarDecidable (t : Tm Φ) (i : Nat) : Decidable (t.UsesVar i) :=
  match t with
  | .var j => inferInstanceAs (Decidable (i = j))
  | .op _ a | .inl a | .inr a | .abort a => usesVarDecidable a i
  | .unit => isFalse id
  | .pair a b =>
    letI := usesVarDecidable a i
    letI := usesVarDecidable b i
    inferInstanceAs (Decidable (_ ∨ _))
  | .let₁ a b =>
    letI := usesVarDecidable a i
    letI := usesVarDecidable b (i + 1)
    inferInstanceAs (Decidable (_ ∨ _))
  | .let₂ a b =>
    letI := usesVarDecidable a i
    letI := usesVarDecidable b (i + 2)
    inferInstanceAs (Decidable (_ ∨ _))
  | .case a l r =>
    letI := usesVarDecidable a i
    letI := usesVarDecidable l (i + 1)
    letI := usesVarDecidable r (i + 1)
    inferInstanceAs (Decidable (_ ∨ _ ∨ _))

end Silmaril.Isotope.LambdaSSA.Tm
