module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummand

/-! # Exact CFG denotation on a common left-tag dispatcher -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open UnusedSummand
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {κ : Type u} (M : TypeModel (Ty κ) V) {Φ : Type v} [HasTy Φ (Ty κ)] [InstructionModel J M Φ]

/-- Compare actual CFG witnesses when substituting the left-tag embedding
for each wide block parameter prunes its row to the common typed row,
with a left tag on every local transfer. The entry uses the same routing
and the outward label list is fixed. The comparison uses the existing
pure uniformity field of the supplied strong Elgot Freyd model. -/
theorem CfgDenotesAt.eq_of_taken_tag {k : Nat} {P : Fin (k + 1) → Ty κ}
    {K : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}
    (D : Fin (k + 1) → Ty κ) (entry : Row (Φ := Φ) P K Γ)
    (rows : ∀ i, Row (Φ := Φ) P K (P i :: Γ)) (raw : Fin (k + 1) → Region Φ)
    (prune : ∀ i, Region.PruneConstructorTests
      ((raw i).substVars (Tm.replaceNewest (.inl (.var 0)))) ((rows i).region true id))
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M K)}
    (small : CfgDenotesAt J M P (entry.region false id) (fun i => (rows i).region false id) f)
    (wide : CfgDenotesAt J M (family P (some D)) (entry.region true id) raw g) : f = g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandProof.taken_tag_agreement
    J M D entry rows raw prune small wide

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
