module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Outer.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgOuterAdmission

/-! # Compare two original exact witnesses of a checked finite outer table -/

public section

universe v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.Outer

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {Φ : Type v} [HasTy Φ (Ty Empty)] {a k n : Nat}
  {outerKeep : Fin 1 ↪ Fin (a + 1)} {innerKeep : Fin (k + 1) ↪ Fin (n + 1)}
  {P : Fin (k + 1) → Ty Empty} {r : Region Φ} {L : LCtx (Ty Empty)}

/-- The checked restriction preserves the original indexed syntax and
bounds. Its retained outer row passes finite nested admission. -/
theorem check?_sound {c : CfgRestriction Φ (a + 1)}
    (ok : check? outerKeep innerKeep P r L = some c) :
    c.Valid outerKeep L.length r ∧ Finite.compare? innerKeep P (c.retained outerKeep) L = .certified :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgOuterAdmission.checked ok

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Φ]

/-- Outer rolling preserves each original arrow before the taken-tag
comparison. The exact witnesses may differ on the omitted outer and
inner types. The supplied outward label context keeps its order. -/
theorem compare?_sound (roll : IterationRolling C) (ok : compare? outerKeep innerKeep P r L = .certified)
    {h h' : r.HasType [] L} {f g : J.obj (ctxObj M []) ⟶ J.obj (labelObj M L)}
    (left : RegionDenotes J M h f) (right : RegionDenotes J M h' g) : f = g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgOuterAdmission.compare J M roll ok left right

end Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.Outer
