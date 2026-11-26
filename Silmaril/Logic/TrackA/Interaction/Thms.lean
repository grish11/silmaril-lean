module

public import Silmaril.Logic.TrackA.Interaction.Defs
import Silmaril.Proofs.Logic.TrackA.Interaction.Institution

@[expose] public section

namespace Silmaril.Logic.TrackA.Interaction

open CategoryTheory Opposite Silmaril.Logic.Institution Silmaril.Semantics.TrackA.Interaction

universe u v w m a b d s i

section RefinementSystem

variable {C : Type u} [Category.{v} C] (system : RefinementSystem.{u,v,w,m} C)

@[simp] theorem RefinementSystem.corridor_id (S : Cᵒᵖ) :
    system.corridor (𝟙 S) = 𝟙 (system.room S) :=
  Proofs.Logic.TrackA.Interaction.corridor_id system S

theorem RefinementSystem.corridor_comp {S T U : Cᵒᵖ} (f : S ⟶ T) (g : T ⟶ U) :
    system.corridor (f ≫ g) = system.corridor f ≫ system.corridor g :=
  Proofs.Logic.TrackA.Interaction.corridor_comp system f g

end RefinementSystem

/-- The checked room functor, whose sentence and model functors are available
through `ClassicInstitution.ofRoomFunctor`. -/
def RefinementSystem.rooms {C : Type u} [Category.{v} C]
    (system : RefinementSystem.{u,v,w,m} C) : Cᵒᵖ ⥤ Room.{w,m,m} where
  obj := system.room
  map := system.corridor
  map_id := system.corridor_id
  map_comp := system.corridor_comp

noncomputable section

/-- Forest satisfaction uses the actual may-observations of each root. -/
def treeInstitution (B : Signature.{b,d}) (A : Type a) (I : Type i) :
    ClassicInstitution (TraceSignature.{u,v}ᵒᵖ) :=
  ClassicInstitution.ofRoomFunctor (treeSystem.{u,v,a,b,d,s,i} B A I).rooms

/-- Trace-set satisfaction is the Track A refinement order. -/
def traceInstitution (A : Type a) : ClassicInstitution (TraceSignature.{u,v}ᵒᵖ) :=
  ClassicInstitution.ofRoomFunctor (traceSystem A).rooms

/-- The same upper-bound semantics with an explicit whole-run UB marker. -/
def explicitInstitution (A : Type a) : ClassicInstitution (TraceSignature.{u,v}ᵒᵖ) :=
  ClassicInstitution.ofRoomFunctor (explicitSystem A).rooms

@[simp] theorem catastrophicCorridor_id (A : Type a) (S : TraceSignature.{u,v}ᵒᵖ) :
    catastrophicCorridor A (𝟙 S) = 𝟙 (catastrophicRoom A S) :=
  Proofs.Logic.TrackA.Interaction.catastrophic_corridor_id A S

theorem catastrophicCorridor_comp (A : Type a) {S T U : TraceSignature.{u,v}ᵒᵖ}
    (f : S ⟶ T) (g : T ⟶ U) :
    catastrophicCorridor A (f ≫ g) = catastrophicCorridor A f ≫ catastrophicCorridor A g :=
  Proofs.Logic.TrackA.Interaction.catastrophic_corridor_comp A f g

/-- Whole-row catastrophic refinement is a fourth institution. -/
def catastrophicInstitution (A : Type a) : ClassicInstitution (TraceSignature.{u,v}ᵒᵖ) :=
  ClassicInstitution.ofRoomFunctor
    { obj := catastrophicRoom A
      map := catastrophicCorridor A
      map_id := catastrophicCorridor_id A
      map_comp := catastrophicCorridor_comp A }

/-- Saturating the exact image agrees with relabeling a previously saturated set. -/
theorem catastrophic_reduct_collapse {S T : TraceSignature.{u,v}} {A : Type a}
    (f : S ⟶ T) (runs : UB.Explicit (Trace S.signature A)) :
    catastrophicReduct f (UB.collapse runs) = UB.collapse ((explicitObservations A).map f '' runs) :=
  Proofs.Logic.TrackA.Interaction.catastrophic_reduct_collapse f runs

/-- The complete forest-to-UB projection commutes with the model reduct. -/
theorem tree_catastrophic_relabel {S T : TraceSignature.{u,v}} {B : Signature.{b,d}}
    {A : Type a} {I : Type i} (f : S ⟶ T) (forest : Forest.{u,v,b,d,a,i,s} S.signature B (Option A) I) :
    (forest.relabel f.hom).toCatastrophic = catastrophicReduct f forest.toCatastrophic := by
  rw [Forest.toCatastrophic, Forest.toCatastrophic, catastrophic_reduct_collapse, Forest.toExplicit_relabel]
  rfl

/-- Taking the set of runs preserves and reflects truth of every trace bound. -/
theorem tree_trace_satisfaction {S : TraceSignature.{u,v}} {B : Signature.{b,d}}
    {A : Type a} {I : Type i} (forest : Forest.{u,v,b,d,a,i,s} S.signature B A I)
    (bound : Set (Trace S.signature A)) :
    (treeInstitution B A I).Sat (op S) (Discrete.mk forest) bound ↔
      (traceInstitution A).Sat (op S) (Discrete.mk forest.observes) bound := Iff.rfl

/-- The UB projection preserves and reflects satisfaction with the explicit
bound pulled back along the classifier. -/
theorem tree_explicit_satisfaction {S : TraceSignature.{u,v}} {B : Signature.{b,d}}
    {A : Type a} {I : Type i} (forest : Forest.{u,v,b,d,a,i,s} S.signature B (Option A) I)
    (bound : UB.Explicit (Trace S.signature A)) :
    (treeInstitution B (Option A) I).Sat (op S) (Discrete.mk forest) (UB.classify ⁻¹' bound) ↔
      (explicitInstitution A).Sat (op S) (Discrete.mk forest.toExplicit) bound :=
  Set.image_subset_iff.symm

/-- A closed catastrophic bound holds exactly when it covers the explicit
behaviors. Saturation may introduce additional ordinary observations. -/
theorem tree_catastrophic_satisfaction {S : TraceSignature.{u,v}} {B : Signature.{b,d}}
    {A : Type a} {I : Type i} (forest : Forest.{u,v,b,d,a,i,s} S.signature B (Option A) I)
    (bound : UB.Catastrophic (Trace S.signature A)) :
    (catastrophicInstitution A).Sat (op S) (Discrete.mk forest.toCatastrophic) bound ↔
      (explicitInstitution A).Sat (op S) (Discrete.mk forest.toExplicit) bound.val :=
  UB.collapse_gc _ _ _

end

end Silmaril.Logic.TrackA.Interaction
