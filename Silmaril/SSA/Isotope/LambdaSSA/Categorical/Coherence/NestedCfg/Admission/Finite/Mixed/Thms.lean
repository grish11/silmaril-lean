module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Mixed.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMixedSyntax
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMixedAdmission

/-! # Exact comparison for an accepted mixed outer dispatcher -/

public section

universe v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.Mixed

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {Φ : Type v} [HasTy Φ (Ty Empty)] {q o k n : Nat}
  {outerKeep : Fin (q + 1) ↪ Fin (o + 1)} {innerKeep : Fin (k + 1) ↪ Fin (n + 1)}
  {P : Fin (k + 1) → Ty Empty} {Q : Fin q → Ty Empty}
  {r : Region Φ} {L : LCtx (Ty Empty)}

/-- Successful admission records the source restriction, the inner and
ordinary route checks, and a written anchor for each ordinary slot. -/
theorem check?_sound {p : Plan Φ q (o + 1) (k + 1) (n + 1)}
    (ok : check? outerKeep innerKeep P Q r L = some p) : p.Valid outerKeep innerKeep P Q r L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMixedSyntax.valid ok

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Φ]

/-- Compare any two exact denotations of the same admitted written graph.
Recover the actual live types from the entry and the anchored transfers,
then assemble the slot squares internally. Both original arrows retain
the supplied ordered exit context. -/
theorem compare?_sound (roll : IterationRolling C) (ok : compare? outerKeep innerKeep P Q r L = .certified)
    {h h' : r.HasType [] L} {f g : J.obj (ctxObj M []) ⟶ J.obj (labelObj M L)}
    (left : RegionDenotes J M h f) (right : RegionDenotes J M h' g) : f = g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMixedAdmission.compare J M roll ok left right

end Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.Mixed
