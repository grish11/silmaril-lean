module

public import Silmaril.Semantics.Calco2019.InductiveResumption.Thms
public import Silmaril.Semantics.Calco2019.ExceptionThms

/-! # The inductive resumption generators and interpretation algebra -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Inductive

open CategoryTheory
variable {C : Type u} [Category.{v} C]

/-- Natural transformations from endofunctors into monads form the bimodule
of the ordinary free-extension statement in §1.3. -/
def monadBimodule (C : Type u) [Category.{v} C] :
    Bimodule (C ⥤ C) (CategoryTheory.Monad C) :=
  Profunctor.ofCore {
    obj U K := K ⟶ (U : C ⥤ C)
    map m a := ↾fun e => a ≫ e ≫ m.toNatTrans
    map_id U K := by
      apply ConcreteCategory.coe_ext
      funext e
      change (𝟙 K) ≫ e ≫ (𝟙 (U : C ⥤ C)) = e
      simp
    map_comp m n a b := by
      apply ConcreteCategory.coe_ext
      funext e
      change (a ≫ b) ≫ e ≫ (m.toNatTrans ≫ n.toNatTrans) =
        a ≫ (b ≫ e ≫ m.toNatTrans) ≫ n.toNatTrans
      simp only [Category.assoc] }

theorem monadBimodule_post {K : C ⥤ C} {U V : CategoryTheory.Monad C}
    (e : (monadBimodule C).Hom K U) (m : U ⟶ V) :
    (monadBimodule C).post e m = (show K ⟶ (U : C ⥤ C) from e) ≫ m.toNatTrans := by
  let a : K ⟶ (U : C ⥤ C) := e
  change (𝟙 K) ≫ a ≫ m.toNatTrans = a ≫ m.toNatTrans
  exact Category.id_comp _

section Generators

variable {C : Type u} [Category.{v} C] (P : Coproducts C)
  {T : CategoryTheory.Monad C} {H : C ⥤ C}
  (R : InitialResumptions (Exception.parametrized P T H))

/-- Lift a base computation into a resumption without performing an operation. -/
def liftBase (X : C) : T.obj X ⟶ R.obj X :=
  T.map (P.inl (Y := H.obj (R.obj X))) ≫ R.roll X

/-- Perform an operation and return the value of the selected branch. -/
def liftStep (X : C) : H.obj X ⟶ R.obj X :=
  H.map (R.unit X) ≫ Exception.raise P T (H.obj (R.obj X)) X ≫ R.roll X

end Generators

variable {C : Type u} [Category.{v} C] (P : Coproducts C)
  {T S : CategoryTheory.Monad C} {H : C ⥤ C}
  (ξ : T ⟶ S) (σ : H ⟶ (S : C ⥤ C))

local notation "A" => KleisliTriple.ofMonad S
local notation "M" => Exception.parametrized P T H

/-- Run an interpreted operation whose branches are already computations. -/
def runOperation (X : C) : H.obj (S.obj X) ⟶ S.obj X :=
  σ.app (S.obj X) ≫ S.μ.app X

/-- The algebra interpreting returns and operations in the target monad. -/
def interpretationAlgebra (X : C) : T.obj (P.sum X (H.obj (S.obj X))) ⟶ S.obj X :=
  ξ.app _ ≫ (A).extend (P.desc (S.η.app X) (runOperation σ X))

/-- Interpret an inductive resumption by its initial-algebra fold. -/
def interpretation (R : InitialResumptions M) (X : C) : R.obj X ⟶ S.obj X :=
  R.fold (interpretationAlgebra P ξ σ X)

end Silmaril.Calco2019.Inductive
