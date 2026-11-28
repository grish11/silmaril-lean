module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Categorical.Realization.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Realization

/-! # Agreement with categorical λSSA region denotation -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Acyclic

open CategoryTheory CategoryTheory.Limits
open LetIter.Semantics.Categorical (TypeModel)

/-- The native positional context and the exact LetCase context differ by
the reversible empty-environment factor and tensor reassociation. -/
theorem contextMap_isIso {τ : Type u} [TypeFormers τ] {V : Type u₁} [Category.{v₁} V]
    [CartesianMonoidalCategory V] [HasFiniteCoproducts V] (M : TypeModel τ V)
    {n : Nat} (β : BoundCtx τ n) : IsIso (contextMap M β) :=
  contextMap_isIso_proof M β

end Silmaril.Isotope.LambdaSSA.Acyclic

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Code

open CategoryTheory CategoryTheory.Limits PremonoidalCategory
open scoped MonoidalCategory
open LetIter.Semantics.Categorical (TypeModel InstructionModel envObj)
open LetIter.ProofRelevant.Semantics.Categorical (duplicate)
open LambdaSSA.Semantics.Categorical (RegionTypingCoherent denoteRegion labelInject)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]

local notation "Env" => envObj M (Ctx.nil : Ctx Empty τ)
local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

/-- The existing λSSA region denotation agrees with the compiled LetCase
denotation after converting the input environment and injecting the selected
exit. The one-block dispatcher of a structured join executes its exit arm
after one block invocation. -/
theorem denote_toSSA {n : Nat} {β : BoundCtx τ n} {A : τ}
    (c : Code Φ β A) {L : LCtx τ} {exit : Nat} (h : At L exit A) :
    denoteRegion J M (c.toSSA_hasType h) =
      J.map (contextMap M β) ≫ LetCase.Semantics.Categorical.denote J M c.toLetCase.2 ≫
        J.map (labelInject M exit h) :=
  denote_toSSA_proof M J c h

/-- Distributing the shared join preserves the arrow of the actual exact
λSSA regions under the same transported-diagonal condition as LetCase. -/
theorem denote_toSSA_distributeJoin {n : Nat} {β : BoundCtx τ n} {A B D E : τ}
    (central : IsCentral (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (e : Operand Φ β (coprod A B)) (l : Code Φ (β.snoc A) D) (r : Code Φ (β.snoc B) D)
    (k : Code Φ (β.snoc D) E) {L : LCtx τ} {exit : Nat} (h : At L exit E) :
    denoteRegion J M ((Code.join (.case e l r) k).toSSA_hasType h) =
      denoteRegion J M ((distributeJoin e l r k).toSSA_hasType h) := by
  rw [denote_toSSA J M _ h, denote_toSSA J M _ h, denote_distributeJoin J M central]

end Silmaril.Isotope.LambdaSSA.Acyclic.Code
