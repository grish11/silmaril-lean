module

public import Silmaril.Logic.Institution.Structured.Constraints.Initial
public import Mathlib.Data.List.Basic

@[expose] public section
namespace Silmaril.Logic.Institution.Structured.Constraints.Applications.Lists
open CategoryTheory
universe u

/-- One explicit interpretation of the paper's informal LIST/TRIV illustration:
two sorts, elements and lists, with nil and cons and no imposed equations.
The paper does not prescribe a unique presentation of these names. -/
structure Algebra where
  Elt : Type u
  Carrier : Type u
  nil : Carrier
  cons : Elt → Carrier → Carrier

namespace Algebra

/-- A map may change both sorts and preserves the two constructors. -/
@[ext] structure Hom (A B : Algebra.{u}) where
  elt : A.Elt → B.Elt
  carrier : A.Carrier → B.Carrier
  map_nil : carrier A.nil = B.nil
  map_cons : ∀ e xs, carrier (A.cons e xs) = B.cons (elt e) (carrier xs)

def id (A : Algebra.{u}) : Hom A A := ⟨_root_.id, _root_.id, rfl, fun _ _ => rfl⟩

def comp {A B C : Algebra.{u}} (f : Hom A B) (g : Hom B C) : Hom A C where
  elt := g.elt ∘ f.elt
  carrier := g.carrier ∘ f.carrier
  map_nil := by simp only [Function.comp_apply, f.map_nil, g.map_nil]
  map_cons := by intro e xs; simp only [Function.comp_apply, f.map_cons, g.map_cons]

instance : Category Algebra.{u} where
  Hom := Hom
  id := id
  comp := comp
  id_comp _ := Hom.ext rfl rfl
  comp_id _ := Hom.ext rfl rfl
  assoc _ _ _ := Hom.ext rfl rfl

end Algebra

/-- TRIV forgets the list carrier but retains the varying element sort. -/
def forget : Algebra.{u} ⥤ Type u where
  obj A := A.Elt
  map f := TypeCat.ofHom f.elt

/-- The free list algebra on an arbitrary element type. -/
def freeObject (E : Type u) : Algebra.{u} := ⟨E, List E, [], List.cons⟩

/-- Element maps act on the free list sort by `List.map`. -/
def free : Type u ⥤ Algebra.{u} where
  obj := freeObject
  map f := ⟨f, List.map f, rfl, fun _ _ => rfl⟩
  map_id E := Algebra.Hom.ext rfl (by funext xs; exact List.map_id xs)
  map_comp f g := Algebra.Hom.ext rfl (by
    funext xs
    change List.map (fun e => g (f e)) xs = List.map g (List.map f xs)
    exact List.map_map.symm)

/-- Evaluate lists with an element map using the target's constructors. -/
def foldHom {E : Type u} (A : Algebra.{u}) (f : E → A.Elt) : freeObject E ⟶ A where
  elt := f
  carrier := List.foldr (fun e xs => A.cons (f e) xs) A.nil
  map_nil := rfl
  map_cons _ _ := rfl

/-- Constructor preservation determines a map from the free algebra uniquely. -/
theorem hom_from_free_unique {E : Type u} {A : Algebra.{u}} (f : freeObject E ⟶ A) :
    foldHom A f.elt = f := by
  refine Algebra.Hom.ext (x := _) (y := _) ?_ ?_
  · rfl
  funext xs
  induction xs with
  | nil => exact f.map_nil.symm
  | cons e xs ih => exact (congrArg (A.cons (f.elt e)) ih).trans (f.map_cons e xs).symm

/-- The actual free/forgetful hom equivalence for both varying sorts. -/
def homEquiv (E : Type u) (A : Algebra.{u}) : (freeObject E ⟶ A) ≃ (E → A.Elt) where
  toFun f := f.elt
  invFun := foldHom A
  left_inv := hom_from_free_unique
  right_inv _ := rfl

/-- Lists are the genuine free extension of an arbitrary element type. -/
def adjunction : free.{u} ⊣ forget.{u} :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun E A => (homEquiv E A).trans TypeCat.homEquiv.symm
    homEquiv_naturality_left_symm := by
      intro E F A f g
      refine Algebra.Hom.ext (x := _) (y := _) ?_ ?_
      · rfl
      funext xs
      induction xs with
      | nil => rfl
      | cons e xs ih => exact congrArg (A.cons (g (f e))) ih
    homEquiv_naturality_right := by
      intro E A B f g
      rfl }

/-- The counit evaluates each algebra's own elements as lists. -/
theorem counit_carrier (A : Algebra.{u}) :
    (adjunction.counit.app A).carrier = List.foldr A.cons A.nil := rfl

/-- The free algebra's counit is its actual identity map. -/
theorem counit_free (E : Type u) : adjunction.counit.app (freeObject E) = 𝟙 (freeObject E) := by
  refine Algebra.Hom.ext (x := _) (y := _) ?_ ?_
  · rfl
  funext xs
  induction xs with
  | nil => rfl
  | cons e xs ih => exact congrArg (List.cons e) ih

/-- The abstract freeness-constraint API recognizes the concrete list model. -/
theorem freeAt_free (E : Type u) : FreeAt forget (freeObject E) := by
  apply (freeAt_iff_counit_isIso adjunction _).2
  rw [counit_free]
  exact ⟨⟨𝟙 (freeObject E), Category.id_comp _, Category.comp_id _⟩⟩

/-- For any list algebra, the abstract constraint is exactly invertibility of
its actual list-evaluation counit. -/
theorem freeAt_iff_evaluation_isIso (A : Algebra.{u}) :
    FreeAt forget A ↔ IsIso (adjunction.counit.app A) :=
  freeAt_iff_counit_isIso adjunction A

/-- An algebra identifying nil with every cons; constructors alone do not imply freeness. -/
def collapsed : Algebra.{u} := ⟨PUnit, PUnit, PUnit.unit, fun _ _ => PUnit.unit⟩

/-- The freeness constraint rejects the collapsed algebra. -/
theorem not_freeAt_collapsed : ¬ FreeAt forget collapsed := by
  intro h
  obtain ⟨f, _⟩ := (h (freeObject PUnit)).surjective (TypeCat.ofHom _root_.id)
  have hn : f.carrier PUnit.unit = [] := f.map_nil
  have hc : f.carrier PUnit.unit = f.elt PUnit.unit :: f.carrier PUnit.unit :=
    f.map_cons PUnit.unit PUnit.unit
  rw [hn] at hc
  cases hc

end Silmaril.Logic.Institution.Structured.Constraints.Applications.Lists
