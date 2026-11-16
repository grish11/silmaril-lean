module

public import Silmaril.Logic.Algebraic.ManySorted.PublicEQ.Thms

/-! The existing private many-sorted syntax and algebras over varying sort sets.
Signature morphisms may identify sorts and operations. No carrier is required
inhabited and every existing algebra homomorphism is retained. -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Algebraic.ManySorted.Varying
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

structure Signature : Type 1 where
  sorts : Type
  algebraic : ManySorted.Signature sorts

structure Signature.Hom (A B : Signature) where
  sorts : A.sorts → B.sorts
  operations : ∀ {n inputs output}, A.algebraic.operations n inputs output →
    B.algebraic.operations n (sorts ∘ inputs) (sorts output)

instance : Category Signature where
  Hom := Signature.Hom
  id _ := ⟨id, fun op => op⟩
  comp f g := ⟨g.sorts ∘ f.sorts, fun op => g.operations (f.operations op)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable {A B C : Signature}

/-- The terms, equations and models remain the independently defined private ones. -/
abbrev Term (A : Signature) {k} (Γ : Fin k → A.sorts) (s : A.sorts) :=
  ManySorted.Term A.algebraic Γ s
abbrev Equation (A : Signature) := ManySorted.Equation A.algebraic
abbrev Model (A : Signature) := ManySorted.Model A.algebraic

def mapTerm (f : A ⟶ B) {k} {Γ : Fin k → A.sorts} {s} :
    Term A Γ s → Term B (f.sorts ∘ Γ) (f.sorts s)
  | .var i => .var i
  | .app op args => .app (f.operations op) (fun i => mapTerm f (args i))

@[simp] theorem mapTerm_id {k} {Γ : Fin k → A.sorts} {s} (t : Term A Γ s) :
    mapTerm (𝟙 A) t = t := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (ManySorted.Term.app op) (funext ih)

@[simp] theorem mapTerm_comp (f : A ⟶ B) (g : B ⟶ C)
    {k} {Γ : Fin k → A.sorts} {s} (t : Term A Γ s) :
    mapTerm (f ≫ g) t = mapTerm g (mapTerm f t) := by
  induction t with
  | var => rfl
  | app op args ih =>
    exact congrArg (ManySorted.Term.app (g.operations (f.operations op))) (funext ih)

def mapEquation (f : A ⟶ B) (e : Equation A) : Equation B :=
  ⟨e.variableCount, f.sorts ∘ e.context, f.sorts e.sort,
    mapTerm f e.lhs, mapTerm f e.rhs⟩

@[simp] theorem mapEquation_id (e : Equation A) : mapEquation (𝟙 A) e = e := by
  cases e
  simp only [mapEquation, mapTerm_id]
  rfl

@[simp] theorem mapEquation_comp (f : A ⟶ B) (g : B ⟶ C) (e : Equation A) :
    mapEquation (f ≫ g) e = mapEquation g (mapEquation f e) := by
  cases e
  simp only [mapEquation, mapTerm_comp]
  rfl

def reduct (f : A ⟶ B) (M : Model B) : Model A where
  carrier s := M.carrier (f.sorts s)
  operation op args := M.operation (f.operations op) args

/-- Reindex all algebra homomorphisms; no injectivity restriction is imposed. -/
def reductFunctor (f : A ⟶ B) : Model B ⥤ Model A where
  obj := reduct f
  map h := ⟨fun s => h.map (f.sorts s), fun op args => h.operation (f.operations op) args⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem eval_map (f : A ⟶ B) (M : Model B) {k} {Γ : Fin k → A.sorts}
    (ρ : ∀ i, M.carrier (f.sorts (Γ i))) {s} (t : Term A Γ s) :
    M.eval ρ (mapTerm f t) = (reduct f M).eval ρ t := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (M.operation (f.operations op)) (funext ih)

theorem satisfaction (f : A ⟶ B) (M : Model B) (e : Equation A) :
    ManySorted.Equation.Satisfies M (mapEquation f e) ↔
      ManySorted.Equation.Satisfies (reduct f M) e := by
  simp only [ManySorted.Equation.Satisfies, mapEquation, eval_map]
  rfl

theorem reduct_id (M : Model A) : reduct (𝟙 A) M = M := by cases M; rfl

theorem reduct_comp (f : A ⟶ B) (g : B ⟶ C) (M : Model C) :
    reduct (f ≫ g) M = reduct f (reduct g M) := rfl

private theorem hom_hext {D : Signature} {M M' N N' : Model D}
    (hM : M = M') (hN : N = N') (f : M ⟶ N) (g : M' ⟶ N')
    (h : HEq f.map g.map) : HEq f g := by
  cases hM; cases hN
  exact heq_of_eq (ManySorted.Model.Hom.ext _ _ (eq_of_heq h))

theorem reductFunctor_id : reductFunctor (𝟙 A) = 𝟭 (Model A) := by
  apply Functor.hext reduct_id
  intro M N h
  exact hom_hext (reduct_id M) (reduct_id N) _ _ HEq.rfl

theorem reductFunctor_comp (f : A ⟶ B) (g : B ⟶ C) :
    reductFunctor (f ≫ g) = reductFunctor g ⋙ reductFunctor f := by
  apply Functor.hext (reduct_comp f g)
  intro M N h
  exact hom_hext (reduct_comp f g M) (reduct_comp f g N) _ _ HEq.rfl

def room (A : Signature) : Room :=
  ⟨Equation A, Cat.of (Model A), ManySorted.Equation.Satisfies⟩

def institution : Signature ⥤ Room where
  obj := room
  map f := ⟨mapEquation f, reductFunctor f, satisfaction f⟩
  map_id _ := Room.hom_ext (funext mapEquation_id) reductFunctor_id
  map_comp f g := Room.hom_ext (funext (mapEquation_comp f g)) (reductFunctor_comp f g)

def inst : Inst := ⟨Signature, institution⟩

/-- Inclusion of the old fixed-sort signature category without changing its objects. -/
def fiber (S : Type) : ManySorted.Signature S ⥤ Signature where
  obj A := ⟨S, A⟩
  map f := ⟨id, f.operations⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem fiber_mapTerm {S} {A B : ManySorted.Signature S} (f : A ⟶ B)
    {k} {Γ : Fin k → S} {s} (t : ManySorted.Term A Γ s) :
    mapTerm ((fiber S).map f) t = ManySorted.Term.map f t := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (ManySorted.Term.app (f.operations op)) (funext ih)

theorem fiber_institution (S : Type) : fiber S ⋙ institution = ManySorted.institution S := by
  apply Functor.hext (F := fiber S ⋙ institution) (G := ManySorted.institution S) (fun _ => rfl)
  intro A B f
  apply heq_of_eq
  apply Room.hom_ext
  · funext e
    change mapEquation ((fiber S).map f) e = ManySorted.Equation.map f e
    cases e
    simp only [mapEquation, ManySorted.Equation.map, fiber_mapTerm]
    rfl
  · rfl

end Silmaril.Logic.Algebraic.ManySorted.Varying
