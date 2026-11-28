module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.MultiNested.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMultiSyntax
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMultiAdmission

/-! # Compare original exact witnesses of a checked multi-nested table -/

public section

universe v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.MultiNested

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

/-- Recover the original source restriction, typed route checks and bounded anchors. -/
theorem check?_sound {m n : Nat} {keep : Fin m ↪ Fin n} {P : Fin m → Ty Empty} {forms : Fin m → Bool}
    {r : Region Φ} {L : LCtx (Ty Empty)} {p : Plan Φ m n}
    {masks : Fin m → Option InnerMask} {tags : Fin m → CaseTag}
    (ok : check? keep P forms r L masks tags = some p) : p.Valid keep P forms r L tags :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMultiSyntax.checked ok

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Φ]

/-- Compare any two original exact denotations of the same written table.
The checker derives the payload agreements and the per-slot equations
for each chosen injection. Selected nested rows keep their native inner
iterations, and actual exits keep their original ordinals. -/
theorem compare?_sound {m n : Nat} {keep : Fin (m + 1) ↪ Fin (n + 1)}
    {P : Fin (m + 1) → Ty Empty} {forms : Fin (m + 1) → Bool} {r : Region Φ} {L : LCtx (Ty Empty)}
    {masks : Fin (m + 1) → Option InnerMask} {tags : Fin (m + 1) → CaseTag}
    (roll : IterationRolling C) (ok : compare? keep P forms r L masks tags = .certified)
    {h h' : r.HasType [] L} {f g : J.obj (ctxObj M []) ⟶ J.obj (labelObj M L)}
    (left : RegionDenotes J M h f) (right : RegionDenotes J M h' g) : f = g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMultiAdmission.compare J M roll ok left right

end Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.MultiNested
