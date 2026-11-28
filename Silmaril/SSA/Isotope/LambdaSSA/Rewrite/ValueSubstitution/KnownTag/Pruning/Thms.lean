module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Pruning

/-! # Pruning cases on known constructor values -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {κ : Type u} (M : TypeModel (Ty κ) V) {Φ : Type v} [HasTy Φ (Ty κ)] [InstructionModel J M Φ]

variable {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)}
  {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}

/-- Constructor tests on already-bound variables may select either tag.
The transport keeps the original computation arrow and exact exit context. -/
theorem _root_.Silmaril.Isotope.LambdaSSA.Region.PruneConstructorTests.denotes
    {r s : Region Φ} (steps : Region.PruneConstructorTests r s) {h : r.HasType Γ L}
    (d : RegionDenotes J M h f) :
    ∃ hs : s.HasType Γ L, RegionDenotes J M hs f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.KnownTag.prune_denotes J M steps d

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
