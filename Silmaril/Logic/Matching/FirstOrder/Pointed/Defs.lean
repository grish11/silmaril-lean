module

public import Silmaril.Logic.Matching.FirstOrder.Thms

/-! Pointwise matching semantics for closed patterns at a fixed result sort.
Every set-valued model of the first-order core is allowed; a model additionally
chooses a result. This is a separate institution from global pattern validity. -/
@[expose] public section
namespace Silmaril.Logic.Matching.FirstOrder.Pointed
open CategoryTheory Silmaril.Logic.Institution
open Algebraic.ManySorted (Signature)
variable {S : Type} {A B C : Signature S} (s : S)

abbrev ClosedPattern (A : Signature S) := Pattern A (k := 0) Fin.elim0 s

structure Model (A : Signature S) where
  base : FirstOrder.Model A
  point : base.carrier s

namespace Model
variable {s}
/-- Core relational homomorphisms that preserve the chosen result. -/
structure Hom (M N : Model s A) where
  base : FirstOrder.Model.Hom M.base N.base
  point : base.map s M.point = N.point

@[ext] theorem Hom.ext {M N : Model s A} (f g : Hom M N)
    (h : f.base = g.base) : f = g := by
  cases f; cases g; cases h; rfl

instance : Category (Model s A) where
  Hom := Hom
  id _ := ⟨⟨fun _ x => x, fun _ _ _ h => h⟩, rfl⟩
  comp f g :=
    { base :=
        { map := fun t x => g.base.map t (f.base.map t x)
          operation := fun op args result h =>
            g.base.operation op _ _ (f.base.operation op args result h) }
      point := by change g.base.map s (f.base.map s _) = _; rw [f.point, g.point] }
  id_comp _ := Hom.ext _ _ (FirstOrder.Model.Hom.ext _ _ rfl)
  comp_id _ := Hom.ext _ _ (FirstOrder.Model.Hom.ext _ _ rfl)
  assoc _ _ _ := Hom.ext _ _ (FirstOrder.Model.Hom.ext _ _ rfl)

def Satisfies (M : Model s A) (p : ClosedPattern s A) : Prop :=
  M.point ∈ M.base.denote (fun i : Fin 0 => Fin.elim0 i) p
end Model

namespace SignatureMap
variable {s}
def reduct (f : A ⟶ B) (M : Model s B) : Model s A :=
  ⟨FirstOrder.SignatureMap.reduct f M.base, M.point⟩

def reductFunctor (f : A ⟶ B) : Model s B ⥤ Model s A where
  obj := reduct f
  map h := ⟨(FirstOrder.SignatureMap.reductFunctor f).map h.base, h.point⟩
  map_id _ := Model.Hom.ext _ _ rfl
  map_comp _ _ := Model.Hom.ext _ _ rfl

theorem satisfaction (f : A ⟶ B) (M : Model s B) (p : ClosedPattern s A) :
    M.Satisfies (Pattern.map f p) ↔ (reduct f M).Satisfies p := by
  change M.point ∈ M.base.denote _ (Pattern.map f p) ↔ _
  rw [FirstOrder.SignatureMap.denote_map]
  rfl

private theorem hom_hext {M M' N N' : Model s A} (hM : M = M') (hN : N = N')
    (f : Model.Hom M N) (g : Model.Hom M' N')
    (h : HEq f.base.map g.base.map) : HEq f g := by
  cases hM; cases hN
  exact heq_of_eq (Model.Hom.ext _ _ (FirstOrder.Model.Hom.ext _ _ (eq_of_heq h)))

theorem reduct_id (M : Model s A) : reduct (𝟙 A) M = M := by
  cases M with
  | mk base point => cases base; rfl

theorem reduct_comp (f : A ⟶ B) (g : B ⟶ C) (M : Model s C) :
    reduct (f ≫ g) M = reduct f (reduct g M) := rfl

theorem reductFunctor_id : reductFunctor (s := s) (𝟙 A) = 𝟭 (Model s A) := by
  apply Functor.hext reduct_id
  intro M N f
  exact hom_hext (reduct_id M) (reduct_id N) _ _ HEq.rfl

theorem reductFunctor_comp (f : A ⟶ B) (g : B ⟶ C) :
    reductFunctor (s := s) (f ≫ g) = reductFunctor g ⋙ reductFunctor f := by
  apply Functor.hext (reduct_comp f g)
  intro M N h
  exact hom_hext (reduct_comp f g M) (reduct_comp f g N) _ _ HEq.rfl
end SignatureMap

def institution : Signature S ⥤ Room where
  obj A := ⟨ClosedPattern s A, Cat.of (Model s A), Model.Satisfies⟩
  map f := ⟨Pattern.map f, SignatureMap.reductFunctor f, SignatureMap.satisfaction f⟩
  map_id _ := by
    apply Room.hom_ext
    · funext p; exact Pattern.map_id p
    · exact SignatureMap.reductFunctor_id
  map_comp f g := by
    apply Room.hom_ext
    · funext p; exact Pattern.map_comp f g p
    · exact SignatureMap.reductFunctor_comp f g

/-- The institution as a bundled `Inst`: its signatures and room functor `institution`, named so
that records and comorphisms can refer to it. -/
def inst (s : S) := (⟨Signature S, institution s⟩ : Silmaril.Logic.Institution.Inst)

/-- The core sentence whose global validity quantifies over every possible point. -/
def closedSentence (p : ClosedPattern s A) : Sentence A := ⟨0, Fin.elim0, s, p⟩

theorem global_iff_all_points (M : FirstOrder.Model A) (p : ClosedPattern s A) :
    Sentence.Satisfies M (closedSentence s p) ↔
      ∀ point : M.carrier s, (Model.mk M point).Satisfies p := by
  constructor
  · intro h point
    exact h (fun i : Fin 0 => Fin.elim0 i) point
  · intro h v point
    have hv : v = (fun i : Fin 0 => Fin.elim0 i) := by funext i; exact Fin.elim0 i
    cases hv
    exact h point
end Silmaril.Logic.Matching.FirstOrder.Pointed
