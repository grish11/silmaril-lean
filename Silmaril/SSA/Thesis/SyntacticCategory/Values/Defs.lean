module

public import Silmaril.SSA.Thesis.SyntacticCategory.Thms
public import Mathlib.CategoryTheory.Widesubcategory

/-! # Pure values in the syntactic λiter category -/

@[expose] public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory

/-- An arrow of the value category has a syntactically pure representative. -/
def pureProperty (S : Sig.{u}) : MorphismProperty (SynCat S) :=
  fun _ _ f => IsPureMor f

instance pureProperty_multiplicative (S : Sig.{u}) : (pureProperty S).IsMultiplicative where
  id_mem := isPureMor_id
  comp_mem := fun _ _ hf hg => IsPureMor.comp hf hg

/-- The one-variable syntactic value category. -/
abbrev ValueCat (S : Sig.{u}) := WideSubcategory (pureProperty S)

/-- Include syntactic value arrows as computation arrows. -/
def values (S : Sig.{u}) : ValueCat S ⥤ SynCat S :=
  wideSubcategoryInclusion (pureProperty S)

open LocallyNameless

variable {S : Sig.{u}}

/-- The syntactic product type. -/
abbrev productObj (A B : SynCat S) : SynCat S :=
  of (tensor A.ty B.ty)

/-- Destructure a pair and return its first component. -/
def first (A B : SynCat S) : productObj A B ⟶ A :=
  mk (HasType.let₂ HasType.newest (.bv (ι := 1)))

/-- Destructure a pair and return its second component. -/
def second (A B : SynCat S) : productObj A B ⟶ B :=
  mk (HasType.let₂ HasType.newest HasType.newest)

/-- Pair term representatives, using congruence to descend to the quotient. -/
def pairArrows {X A B : SynCat S} (f : X ⟶ A) (g : X ⟶ B) : X ⟶ productObj A B :=
  Quotient.map₂
    (fun a b => ⟨.pair a.1 b.1,
      a.2.elim fun ha => b.2.elim fun hb => ⟨.pair ha hb⟩⟩)
    (fun _ _ ha _ _ hb => Eqv.pair ha hb) f g

end Silmaril.Thesis.LambdaIter.Syn.SynCat
