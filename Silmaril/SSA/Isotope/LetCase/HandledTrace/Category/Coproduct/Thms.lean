module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Coproduct.Defs
import Silmaril.Proofs.SSA.Isotope.LetCase.HandledTrace.Category.Coproduct.Laws

@[expose] public section

namespace Silmaril.Isotope.LetCase.HandledTrace

open CategoryTheory CategoryTheory.Limits Silmaril.Isotope.Semantics Silmaril.Elgot.ITree
open Silmaril.Isotope.Refinement.Models (ChosenCoproducts)

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}

namespace Program

variable {A B C : τ}

/-- The written left injection returns its tagged payload without an exchange. -/
theorem run_inl (a : D A) :
    (inl (Φ := Φ) A B).run M a = pure ((CoproductModel.coprodEquiv A B).symm (.inl a)) :=
  CoproductProofs.run_inl a

/-- The written right injection returns its tagged payload without an exchange. -/
theorem run_inr (b : D B) :
    (inr (Φ := Φ) A B).run M b = pure ((CoproductModel.coprodEquiv A B).symm (.inr b)) :=
  CoproductProofs.run_inr b

/-- Native copairing runs exactly the arm selected by the input's typed tag. -/
theorem run_desc (left : Program Φ A C) (right : Program Φ B C) (x : D (coprod A B)) :
    (left.desc right).run M x =
      Sum.elim (left.run M) (right.run M) (CoproductModel.coprodEquiv A B x) :=
  CoproductProofs.run_desc left right x

end Program

namespace Arrow

variable {A B C : Interface M policy}

/-- The native case operation descends to the observational classes of arms. -/
def desc : (A ⟶ C) → (B ⟶ C) → (A.sum B ⟶ C) :=
  Quotient.map₂' Program.desc (by
    intro left left' hl right right' hr
    exact ⟨CoproductProofs.desc_mono hl.1 hr.1, CoproductProofs.desc_mono hl.2 hr.2⟩)

@[simp] theorem desc_ofProgram (left : Program Φ A.ty C.ty) (right : Program Φ B.ty C.ty) :
    desc (ofProgram (A := A) (B := C) left) (ofProgram (A := B) (B := C) right) =
      ofProgram (left.desc right) :=
  rfl

@[simp] theorem inl_desc (left : A ⟶ C) (right : B ⟶ C) :
    inl A B ≫ desc left right = left :=
  Quotient.inductionOn₂ left right fun l r => Quotient.sound (CoproductProofs.inl_desc l r)

@[simp] theorem inr_desc (left : A ⟶ C) (right : B ⟶ C) :
    inr A B ≫ desc left right = right :=
  Quotient.inductionOn₂ left right fun l r => Quotient.sound (CoproductProofs.inr_desc l r)

/-- The two injections detect precisely the order on the sum hom. Each
restriction keeps the same typed payload and initial handler state. -/
theorem sum_le_iff {f g : A.sum B ⟶ C} :
    f ≤ g ↔ inl A B ≫ f ≤ inl A B ≫ g ∧ inr A B ≫ f ≤ inr A B ≫ g :=
  Quotient.inductionOn₂ f g fun _ _ => CoproductProofs.refines_sum_iff

@[simp] theorem desc_eta (f : A.sum B ⟶ C) : desc (inl A B ≫ f) (inr A B ≫ f) = f := by
  apply le_antisymm <;> rw [sum_le_iff] <;> simp

theorem desc_mono {l l' : A ⟶ C} {r r' : B ⟶ C} (hl : l ≤ l') (hr : r ≤ r') :
    desc l r ≤ desc l' r' :=
  sum_le_iff.mpr (by simpa only [inl_desc, inr_desc] using And.intro hl hr)

/-- Precomposition with the native injections is an order isomorphism.
Its inverse is the native selected-arm copairing. -/
def sumOrderIso (A B C : Interface M policy) : (A.sum B ⟶ C) ≃o ((A ⟶ C) × (B ⟶ C)) where
  toFun f := (inl A B ≫ f, inr A B ≫ f)
  invFun arms := desc arms.1 arms.2
  left_inv := desc_eta
  right_inv arms := Prod.ext (inl_desc arms.1 arms.2) (inr_desc arms.1 arms.2)
  map_rel_iff' := sum_le_iff.symm

/-- A program out of the native empty type has no typed input to observe. -/
theorem abort_unique (f : Interface.zero ⟶ C) : f = abort C :=
  CoproductProofs.empty_hom_eq f (abort C)

end Arrow

/-- The chosen cocone retains the written pure injections. -/
def sumIsColimit (A B : Interface M policy) :
    IsColimit (BinaryCofan.mk (Arrow.inl A B) (Arrow.inr A B)) :=
  BinaryCofan.IsColimit.mk _ Arrow.desc Arrow.inl_desc Arrow.inr_desc
    (fun _ _ h hl hr => (Arrow.desc_eta h).symm.trans (congrArg₂ Arrow.desc hl hr))

/-- The chosen initial map is the written abort on the empty input slot. -/
def zeroIsInitial : IsInitial (Interface.zero (M := M) (policy := policy)) :=
  IsInitial.ofUniqueHom Arrow.abort (fun _ f => Arrow.abort_unique f)

/-- The native sum and empty types supply the existing chosen coproduct interface. -/
def chosenCoproducts : ChosenCoproducts (Interface M policy) where
  sum := Interface.sum
  zero := Interface.zero
  inl := Arrow.inl
  inr := Arrow.inr
  isColimit := sumIsColimit
  isInitial := zeroIsInitial

instance : HasBinaryCoproducts (Interface M policy) :=
  chosenCoproducts.hasBinaryCoproducts

instance : HasInitial (Interface M policy) :=
  chosenCoproducts.hasInitial

end Silmaril.Isotope.LetCase.HandledTrace
