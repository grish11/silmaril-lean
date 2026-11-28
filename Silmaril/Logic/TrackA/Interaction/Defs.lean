module

public import Silmaril.Logic.Institution.Basic
public import Silmaril.Semantics.TrackA.Interaction.Relabel.Thms
public import Mathlib.CategoryTheory.Discrete.Basic

/-! # Refinement institutions for dependent interaction -/

@[expose] public section

namespace Silmaril.Logic.TrackA.Interaction

open CategoryTheory Opposite Silmaril.Logic.Institution Silmaril.Semantics.TrackA.Interaction

universe u v w m a b d s i

/-- The category of all dependent request/reply maps. Composition keeps the
source request in scope throughout the two backward response maps. -/
instance : Category.{max u v} Signature.{u,v} where
  Hom := Signature.Hom
  id := Signature.Hom.id
  comp f g := g.comp f
  id_comp := Signature.Hom.comp_id
  comp_id := Signature.Hom.id_comp
  assoc f g h := (Signature.Hom.comp_assoc f g h).symm

/-- The same objects with the per-request bijectivity condition on arrows.
Forward requests may still identify different operations. -/
structure TraceSignature where
  signature : Signature.{u,v}

instance : Category.{max u v} TraceSignature.{u,v} where
  Hom S T := Signature.TraceHom S.signature T.signature
  id S := Signature.TraceHom.id S.signature
  comp f g := g.comp f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Include the restricted arrows into all dependent signature morphisms. -/
def forgetTraceSignature : TraceSignature.{u,v} ⥤ Signature.{u,v} where
  obj := TraceSignature.signature
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Data for an institution of upper bounds on observations. The model and
observation actions here run in the direction of execution relabeling. -/
structure RefinementSystem (C : Type u) [Category.{v} C] where
  Observation : C ⥤ Type w
  Model : C ⥤ Type m
  observes (S : C) : Model.obj S → Set (Observation.obj S)
  observes_map {S T : C} (f : S ⟶ T) (model : Model.obj S) :
    observes T (Model.map f model) = Observation.map f '' observes S model

namespace RefinementSystem

variable {C : Type u} [Category.{v} C] (system : RefinementSystem.{u,v,w,m} C)

/-- Sentences are upper bounds and model categories are discrete. -/
def room (S : Cᵒᵖ) : Room.{w,m,m} :=
  ⟨Set (system.Observation.obj S.unop), Cat.of (Discrete (system.Model.obj S.unop)),
    fun model bound => system.observes S.unop model.as ⊆ bound⟩

def corridor {S T : Cᵒᵖ} (f : S ⟶ T) : system.room S ⟶ system.room T where
  sen bound := system.Observation.map f.unop ⁻¹' bound
  mod := Discrete.functor fun model => Discrete.mk (system.Model.map f.unop model)
  sat model bound := by
    change system.observes T.unop model.as ⊆ system.Observation.map f.unop ⁻¹' bound ↔
      system.observes S.unop (system.Model.map f.unop model.as) ⊆ bound
    rw [system.observes_map]
    exact Set.image_subset_iff.symm

end RefinementSystem

noncomputable section

/-- Completed finite and infinite traces, with a fixed result type. -/
def traces (A : Type a) : TraceSignature.{u,v} ⥤ Type (max u v a) where
  obj S := Trace S.signature A
  map f := TypeCat.ofHom (Trace.relabel (A := A) f)
  map_id _ := congrArg TypeCat.ofHom (funext Trace.relabel_id)
  map_comp f g := congrArg TypeCat.ofHom (funext (Trace.relabel_comp f g))

/-- Powersets act covariantly on model runs by direct image. -/
def directImage : Type w ⥤ Type w where
  obj := Set
  map f := TypeCat.ofHom (Set.image f)
  map_id _ := congrArg TypeCat.ofHom Set.image_id_eq
  map_comp f g := congrArg TypeCat.ofHom (funext (Set.image_comp g f))

/-- Both the choice signature and the root indexing type are fixed along a
change of effect signature. The state carrier is kept by relabeling. -/
def forestModels (B : Signature.{b,d}) (A : Type a) (I : Type i) :
    TraceSignature.{u,v} ⥤ Type (max (s + 1) u v b d a i) where
  obj S := Forest.{u,v,b,d,a,i,s} S.signature B A I
  map f := TypeCat.ofHom (Forest.relabel (B := B) (A := A) (I := I) f.hom)
  map_id _ := congrArg TypeCat.ofHom (funext Forest.relabel_id)
  map_comp f g := congrArg TypeCat.ofHom (funext (Forest.relabel_comp f.hom g.hom))

def treeSystem (B : Signature.{b,d}) (A : Type a) (I : Type i) :
    RefinementSystem.{max (u + 1) (v + 1), max u v, max u v a, max (s + 1) u v b d a i}
      TraceSignature.{u,v} where
  Observation := traces A
  Model := forestModels.{u,v,a,b,d,s,i} B A I
  observes _ forest := forest.observes
  observes_map f forest := Forest.observes_relabel f forest

/-- Trace-set models permit arbitrary sets, including specifications without a
known realizable tree. -/
def traceSystem (A : Type a) : RefinementSystem TraceSignature.{u,v} where
  Observation := traces A
  Model := traces A ⋙ directImage
  observes _ := id
  observes_map _ _ := rfl

/-- `none` is the whole-run UB marker. `some t` retains the ordinary trace. -/
def explicitObservations (A : Type a) : TraceSignature.{u,v} ⥤ Type (max u v a) where
  obj S := Option (Trace S.signature A)
  map f := TypeCat.ofHom (Option.map (Trace.relabel (A := A) f))
  map_id S := congrArg TypeCat.ofHom (show
    Option.map (Trace.relabel (A := A) (Signature.TraceHom.id S.signature)) = id from
    funext fun t => by cases t <;> simp)
  map_comp f g := congrArg TypeCat.ofHom (show
    Option.map (Trace.relabel (A := A) (g.comp f)) =
      Option.map (Trace.relabel g) ∘ Option.map (Trace.relabel f) from
    funext fun t => by cases t <;> simp [Trace.relabel_comp f g])

def explicitSystem (A : Type a) : RefinementSystem TraceSignature.{u,v} where
  Observation := explicitObservations A
  Model := explicitObservations A ⋙ directImage
  observes _ := id
  observes_map _ _ := rfl


section Catastrophic

variable {A : Type a} {S T : TraceSignature.{u,v}}

/-- The inverse image of a closed bound is closed because `none` maps to `none`. -/
def catastrophicTranslate (f : S ⟶ T) (bound : UB.Catastrophic (Trace T.signature A)) :
    UB.Catastrophic (Trace S.signature A) :=
  ⟨(explicitObservations A).map f ⁻¹' bound.val, fun hasUB => by
    rw [bound.property hasUB]
    exact Set.preimage_univ⟩

/-- Relabel a saturated model by taking the image and saturating in the target.
A target request outside the image is still permitted when the row has UB. -/
def catastrophicReduct (f : S ⟶ T) (model : UB.Catastrophic (Trace S.signature A)) :
    UB.Catastrophic (Trace T.signature A) :=
  UB.collapse ((explicitObservations A).map f '' model.val)

theorem catastrophic_gc (f : S ⟶ T) :
    GaloisConnection (catastrophicReduct (A := A) f) (catastrophicTranslate f) :=
  by
    intro model bound
    exact (UB.collapse_gc _ _ _).trans Set.image_subset_iff

/-- Models and sentences are saturated sets, ordered by inclusion in satisfaction. -/
def catastrophicRoom (A : Type a) (S : TraceSignature.{u,v}ᵒᵖ) :
    Room.{max u v a, max u v a, max u v a} :=
  ⟨UB.Catastrophic (Trace S.unop.signature A), Cat.of (Discrete (UB.Catastrophic
    (Trace S.unop.signature A))), fun model bound => model.as ≤ bound⟩

def catastrophicCorridor (A : Type a) {S T : TraceSignature.{u,v}ᵒᵖ} (f : S ⟶ T) :
    catastrophicRoom A S ⟶ catastrophicRoom A T where
  sen := catastrophicTranslate f.unop
  mod := Discrete.functor fun model => Discrete.mk (catastrophicReduct f.unop model)
  sat _ _ := (catastrophic_gc f.unop _ _).symm

end Catastrophic

end

end Silmaril.Logic.TrackA.Interaction
