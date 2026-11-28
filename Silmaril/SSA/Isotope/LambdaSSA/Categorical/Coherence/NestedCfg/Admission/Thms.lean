module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgAdmissionSyntax
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgAdmission

/-! # Certified comparison of two original nested CFG witnesses -/

public section

universe v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.NestedAdmission

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

/-- A successful check gives the written no-target, left-case and typed
constructor-route evidence used by semantic comparison. -/
theorem check?_sound {r : Region Φ} {p : Plan Φ} (ok : check? r = some p) : p.Valid r :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgAdmissionSyntax.valid ok

/-- An unsupported region produces unknown. -/
theorem compare?_unknown {r : Region Φ} (h : check? r = none) : compare? r = .unknown := by
  simp [compare?, h]

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Φ]

/-- For an admitted written CFG, compare any two original exact witnesses.
Their selected internal families may differ. The proof uses the graph
model's own rolling, pure uniformity and outward naturality. -/
theorem compare?_sound (roll : IterationRolling C) {r : Region Φ}
    {h h' : r.HasType [] exits}
    {f g : J.obj (ctxObj M []) ⟶ J.obj (labelObj M exits)}
    (ok : compare? r = .certified) (left : RegionDenotes J M h f) (right : RegionDenotes J M h' g) :
    f = g := by
  cases checked : check? r with
  | none => simp [compare?, checked] at ok
  | some p =>
      exact Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgAdmission.compare J M roll
        (check?_sound checked) left right

end Silmaril.Isotope.LambdaSSA.NestedAdmission
