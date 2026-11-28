module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Readback.Thms

/-! # The reflection statement for packed single-feedback dispatchers

`Valid` is equality of arrows in every model of the supported class. It
does not mention an interpreter, a reply policy or a finite test.
`Reflects` asks that this equality already holds in the quotient.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep)
open Paper.Extension.Singleton (ofRegion)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- Two typed regions have one arrow in every locally small coherent
shared-tensor, central-unit strong Elgot Freyd model. This is the model
class of `Eqv.sound`. -/
def Valid {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (hr : HasType Γ r L) (hs : HasType Γ s L) :
    Prop :=
  ∀ {V C : Type 1} [Category.{0} V] [Category.{0} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    [Iteration C] [ElgotCategory C] (J : V ⥤ C)
    [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
    (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M],
    (∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h) →
    denoteRegion J M hr = denoteRegion J M hs

/-- Reflection at two guarded regions with one capture: validity in every
model implies the contextual equation of this quotient. -/
def Reflects {X : τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches [X] r L) (hs : ValueBranches [X] s L) : Prop :=
  Valid hr.hasType hs.hasType → Eqv pe [X] r s L

/-- Reflection on the normalized fragment: all packed single-feedback
dispatcher representatives of nonempty guarded tables at one capture `X`
and one exit `D`. The two tables may differ in arity and row types. -/
def PackedReflection (X D : τ) : Prop :=
  ∀ {n m : Nat} (R : Fin (n + 1) → τ) (S : Fin (m + 1) → τ)
    {e e' : Region Φ} {blocks : Fin (n + 1) → Region Φ} {blocks' : Fin (m + 1) → Region Φ}
    (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D]))
    (he' : ValueBranches [X] e' (List.ofFn S ++ [D]))
    (hb' : ∀ i, ValueBranches [S i, X] (blocks' i) (List.ofFn S ++ [D])),
    Reflects pe (packedReadbackRep R he hb).property (packedReadbackRep S he' hb').property

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking
