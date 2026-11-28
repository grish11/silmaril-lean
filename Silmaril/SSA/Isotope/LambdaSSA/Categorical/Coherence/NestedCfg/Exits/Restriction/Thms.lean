module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Thms

/-! # Outward payload maps after sparse internal restriction -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {κ : Type u} (M : TypeModel (Ty κ) V) {Φ : Type v} [HasTy Φ (Ty κ)] [InstructionModel J M Φ]

/-- Compare the original arrows after restricting each internal family
separately. The retained types agree and the outward map acts on their
typed transfers. The full families may give removed slots different types. -/
theorem CfgDenotesAt.postmap_of_restricted_routes {Γ : VCtx (Ty κ)} {L K : LCtx (Ty κ)} {k n : Nat}
    (keep : Fin (k + 1) ↪ Fin (n + 1)) {S T : Fin (n + 1) → Ty κ}
    (aligned : (fun i => T (keep i)) = (fun i => S (keep i))) (roll : IterationRolling C)
    (out : labelObj M L ⟶ labelObj M K)
    {entry entry' : Region Φ} {rows rows' : Fin (n + 1) → Region Φ}
    (entryScope : entry.LabelsBound (k + 1 + L.length))
    (entryScope' : entry'.LabelsBound (k + 1 + K.length))
    (rowScope : ∀ i, (rows i).LabelsBound (k + 1 + L.length))
    (rowScope' : ∀ i, (rows' i).LabelsBound (k + 1 + K.length))
    (entryRoutes : RegionDenotes.Routes M
      (labelAppendSplit M (List.ofFn (fun i => S (keep i))) L ≫ coprod.map out (𝟙 _))
      (labelAppendSplit M (List.ofFn (fun i => S (keep i))) K) J Γ entry entry')
    (rowRoutes : ∀ i, RegionDenotes.Routes M
      (labelAppendSplit M (List.ofFn (fun i => S (keep i))) L ≫ coprod.map out (𝟙 _))
      (labelAppendSplit M (List.ofFn (fun i => S (keep i))) K)
        J (S (keep i) :: Γ) (rows (keep i)) (rows' (keep i)))
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    {g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M K)}
    (small : CfgDenotesAt J M S (entry.renameLabels (retainLabelIndex keep))
      (fun i => (rows i).renameLabels (retainLabelIndex keep)) f)
    (wide : CfgDenotesAt J M T (entry'.renameLabels (retainLabelIndex keep))
      (fun i => (rows' i).renameLabels (retainLabelIndex keep)) g) :
    g = f ≫ J.map out :=
  CfgDenotesAt.postmap_of_routes J M _ out entryRoutes rowRoutes
    (small.restrict J M keep S roll entryScope rowScope)
    (aligned ▸ wide.restrict J M keep T roll entryScope' rowScope')

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
