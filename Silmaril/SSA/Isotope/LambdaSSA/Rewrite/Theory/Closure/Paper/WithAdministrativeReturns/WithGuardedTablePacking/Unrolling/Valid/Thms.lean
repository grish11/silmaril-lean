module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Unrolling.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.ValidUnrolling

/-! # Every supported model validates unrolling at every round count

`Valid` here is the class of `Eqv.sound`: coherent shared-tensor,
central-unit strong Elgot Freyd models. The proof is a calculation in an
arbitrary such model. It is not a derivation in the quotient, and `Eqv`
for a round count outside the products of twos and threes stays open.
So at such a count reflection is exactly the missing quotient law.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.Extension.Singleton.Rounds
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε) {A B : τ}

section Model

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
    Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)

include pe shared in
/-- In one model of the class, at any universe levels: the written loop on
`n + 1` rounds of a guarded step has the arrow of the loop on one round.
The model assumptions are those of `Eqv.sound` and no others. Inside,
iteration is unrolled by `iterate_roundsStep`, which uses the fixpoint,
naturality and codiagonal laws and uniformity along pure maps. -/
theorem denote_unrolled {s : Region Φ} (hs : ValueBranches [A] s [Silmaril.coprod B A]) (n : Nat) :
    denoteRegion J M (SyntacticCategory.iterateRegion_valueBranches (roundsRegion_typed hs n)).hasType =
      denoteRegion J M (SyntacticCategory.iterateRegion_valueBranches hs).hasType :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.denote_rounds pe J M shared hs n

end Model

include pe in
/-- The two written loops are valid at every round count. -/
theorem valid_unrolled {s : Region Φ} (hs : ValueBranches [A] s [Silmaril.coprod B A]) (n : Nat) :
    Valid (SyntacticCategory.iterateRegion_valueBranches (roundsRegion_typed hs n)).hasType
      (SyntacticCategory.iterateRegion_valueBranches hs).hasType :=
  fun J _ _ M _ _ shared => denote_unrolled pe J M shared hs n

/-- The unrolling law of this quotient for a round count is reflection at
all its written loop pairs. -/
theorem unrolls_iff_reflects (n : Nat) :
    Unrolls (Step (τ := τ) (Φ := Φ) pe) n ↔
      ∀ {A B : τ} {s : Region Φ} (hs : ValueBranches [A] s [Silmaril.coprod B A]),
        Reflects pe (SyntacticCategory.iterateRegion_valueBranches (roundsRegion_typed hs n))
          (SyntacticCategory.iterateRegion_valueBranches hs) :=
  ⟨fun law _ _ _ hs _ => Paper.Extension.Singleton.Rounds.unrolled_eqv _ law hs,
    fun h => (unrolls_iff _ n).2 (fun hs => h hs (valid_unrolled pe hs n))⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking
