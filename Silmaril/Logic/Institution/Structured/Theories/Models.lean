module

public import Silmaril.Logic.Institution.Structured.Theories.Colimits
public import Mathlib.CategoryTheory.Adjunction.Basic

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.Structured.SemanticModels
open CategoryTheory Opposite Silmaril.Logic.Institution
universe u v s p q
variable {Sign : Type u} [Category.{v} Sign] (I : Sign ⥤ Room.{s,p,q})

/-- Models of the actual presentation, as a full subcategory of its signature's
model category. This uses its axioms directly rather than replacing the object
with a closed theory (Durán–Meseguer 1999, §2). -/
abbrev Models (T : Spec I) := (Theory.modelsProperty T.axioms).FullSubcategory

/-- Semantic theory maps preserve satisfaction of the source axioms. -/
theorem reduct_mem {T T' : Spec I} (f : T ⟶ T') (M : Models I T') :
    Theory.modelsProperty T.axioms ((I.map f.sig).mod.obj M.obj) := by
  intro φ hφ
  exact ((I.map f.sig).sat M.obj φ).1 (f.mapsTo hφ M.obj M.property)

/-- The reduct acts on model morphisms through the full-subcategory lift. -/
def reduct {T T' : Spec I} (f : T ⟶ T') : Models I T' ⥤ Models I T :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ (I.map f.sig).mod) (reduct_mem I f)

/-- Restrict the original room to models satisfying a semantic presentation. -/
def room (T : Spec I) : Room.{s,p,q} :=
  ⟨(I.obj T.sig).Sen, Cat.of (Models I T), fun M φ => (I.obj T.sig).Sat M.obj φ⟩

/-- Restrict a corridor along a semantic theory map. -/
def corridor {T T' : Spec I} (f : T ⟶ T') : room I T ⟶ room I T' :=
  ⟨(I.map f.sig).sen, reduct I f, fun M φ => (I.map f.sig).sat M.obj φ⟩

theorem corridor_id (T : Spec I) : corridor I (𝟙 T) = 𝟙 (room I T) := by
  apply Room.hom_ext
  · change (I.map (𝟙 T.sig)).sen = id
    rw [I.map_id]
    rfl
  · exact Theory.lift_ι_comp_eq_id _ _ (by
      change (I.map (𝟙 T.sig)).mod = 𝟭 _
      rw [I.map_id]
      rfl) _

theorem corridor_comp {T T' T'' : Spec I} (f : T ⟶ T') (g : T' ⟶ T'') :
    corridor I (f ≫ g) = corridor I f ≫ corridor I g := by
  apply Room.hom_ext
  · change (I.map (f.sig ≫ g.sig)).sen = (I.map g.sig).sen ∘ (I.map f.sig).sen
    rw [I.map_comp]
    rfl
  · exact Theory.lift_ι_comp_eq_comp _ _ _ _ _ _ (by
      change (I.map (f.sig ≫ g.sig)).mod = (I.map g.sig).mod ⋙ (I.map f.sig).mod
      rw [I.map_comp]
      rfl) _ _ _

/-- Reduct along a composite is the composite of the two reducts. -/
theorem reduct_comp {T T' T'' : Spec I} (f : T ⟶ T') (g : T' ⟶ T'') :
    reduct I (f ≫ g) = reduct I g ⋙ reduct I f :=
  congrArg (fun c => c.mod) (corridor_comp I f g)

/-- The actual institution on semantic presentations, retaining their original
sets of axioms and full model subcategories. -/
def institution : Spec I ⥤ Room.{s,p,q} where
  obj := room I
  map := corridor I
  map_id := corridor_id I
  map_comp := corridor_comp I

/-- The model functor on the paper's theory category. -/
def modelFunctor : (Spec I)ᵒᵖ ⥤ Cat.{p,q} :=
  Silmaril.Logic.Institution.modelFunctor (institution I)

/-- Every original model inhabits the empty presentation's model category;
this supplies populated examples without any satisfiability assumption on
nonempty axiom sets. -/
def emptyModel (S : Sign) (M : (I.obj S).Mod) : Models I ⟨S, ∅⟩ :=
  ⟨M, fun _ h => False.elim h⟩

/-- Every reduct along a semantic theory map has a left adjoint (§2).
This quantifies over all maps, not just signature maps with empty axioms. -/
def Liberal : Prop :=
  ∀ {T T' : Spec I} (f : T ⟶ T'), (reduct I f).IsRightAdjoint

/-- The contravariant model functor sends small theory colimits to limits;
written covariantly with values in `Catᵒᵖ`, as in the paper (§2). -/
def Exact : Prop :=
  CategoryTheory.Limits.PreservesColimitsOfSize.{u,u} (institution I ⋙ Room.modFunctor)

/-- Models of a presentation satisfy exactly the same sentences after semantic
closure. This establishes that the raw presentation model categories are
populated whenever the corresponding closed theory has a model. -/
theorem modelsProperty_closure (T : Spec I) :
    Theory.modelsProperty ((I.obj T.sig).closure T.axioms) =
      Theory.modelsProperty T.axioms := by
  funext M
  apply propext
  constructor
  · intro h φ hφ
    exact h φ ((I.obj T.sig).subset_closure _ hφ)
  · intro h φ hφ
    exact hφ M h

end Silmaril.Logic.Institution.Structured.SemanticModels
