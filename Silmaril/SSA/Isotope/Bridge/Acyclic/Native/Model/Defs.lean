module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Recognition.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Categorical.Realization.Thms
public import Silmaril.SSA.Isotope.LetCase.Structural.Finite.Thms

/-! # Common categorical model class for outward ΛSSA and finite LetCase -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open CategoryTheory CategoryTheory.Limits
open LambdaSSA.Semantics.Categorical (denoteRegion RegionTypingCoherent)
open LetIter.Semantics.Categorical (TypeModel InstructionModel TypingCoherent)
open LetCase.Structural.Finite (Types Context)
open scoped MonoidalCategory LetCase.Structural.Finite LetSeq.StraightLine.Structural

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {n : Nat} {β : Context n} {A : Types}

/-- Validity compares arrows of the original typed regions in the locally
small shared-tensor, central-unit strong Elgot Freyd class. Both native
region and LetIter expression witnesses are coherent. All primitives are
effectful in the syntax, so there is no pure-primitive side condition. -/
def Endpoint.Valid (p q : Endpoint Φ β A) : Prop :=
  ∀ {V C : Type 1} [Category.{0} V] [Category.{0} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    [Iteration C] [ElgotCategory C] (J : V ⥤ C)
    [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
    (M : TypeModel Types V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M],
    TypingCoherent (ν := Empty) J M Φ →
    (∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h) →
    denoteRegion J M p.typed = denoteRegion J M q.typed

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
