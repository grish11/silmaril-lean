module

public import Silmaril.Logic.Separation.Parameterized.Transport.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation.Parameterized
open CategoryTheory Silmaril.Logic.Institution
variable {A B C : Signature}

/-- Closed recursive profiles, with arbitrary universally quantified value
contextSize. Entailment holds at every valuation and every actual resource. -/
structure Sentence (A : Signature) where
  contextSize : Nat
  profiles : Fin 0 → Nat
  pre : Pattern A profiles contextSize
  post : Pattern A profiles contextSize

def Sentence.map (f : A ⟶ B) (p : Sentence A) : Sentence B :=
  ⟨p.contextSize,p.profiles,p.pre.map f,p.post.map f⟩

def Sentence.Satisfies (M : Model A) (p : Sentence A) : Prop :=
  p.pre.denote M (fun i => i.elim0) ⊆ p.post.denote M (fun i => i.elim0)

@[simp] theorem Sentence.map_id (p : Sentence A) : p.map (𝟙 A) = p := by
  cases p
  simp only [map,Pattern.map_id]

@[simp] theorem Sentence.map_comp (f : A ⟶ B) (g : B ⟶ C) (p : Sentence A) :
    p.map (f ≫ g) = (p.map f).map g := by
  cases p
  simp only [map,Pattern.map_comp]

theorem Sentence.satisfaction (f : A ⟶ B) (M : Model B) (p : Sentence A) :
    (p.map f).Satisfies M ↔ p.Satisfies (reduct f M) := by
  unfold Satisfies map
  rw [Pattern.denote_map,Pattern.denote_map]

theorem reduct_id (M : Model A) : reduct (𝟙 A) M = M := by cases M; rfl

theorem reduct_comp (f : A ⟶ B) (g : B ⟶ C) (M : Model C) :
    reduct (f ≫ g) M = reduct f (reduct g M) := rfl

private theorem hom_hext {M M' N N' : Model A} (hm : M = M') (hn : N = N')
    (f : Model.Hom M N) (g : Model.Hom M' N')
    (hv : HEq f.value g.value) (hr : HEq f.resource g.resource) : HEq f g := by
  cases hm
  cases hn
  exact heq_of_eq (Model.Hom.ext _ _ (eq_of_heq hv) (eq_of_heq hr))

theorem reductFunctor_id : reductFunctor (𝟙 A) = 𝟭 (Model A) := by
  apply Functor.hext reduct_id
  intro M N h
  exact hom_hext (reduct_id M) (reduct_id N) _ _ HEq.rfl HEq.rfl

theorem reductFunctor_comp (f : A ⟶ B) (g : B ⟶ C) :
    reductFunctor (f ≫ g) = reductFunctor g ⋙ reductFunctor f := by
  apply Functor.hext (reduct_comp f g)
  intro M N h
  exact hom_hext (reduct_comp f g M) (reduct_comp f g N) _ _ HEq.rfl HEq.rfl

def institution : Signature ⥤ Room where
  obj A := ⟨Sentence A,Cat.of (Model A),Sentence.Satisfies⟩
  map f := ⟨Sentence.map f,reductFunctor f,Sentence.satisfaction f⟩
  map_id _ := Room.hom_ext (funext Sentence.map_id) reductFunctor_id
  map_comp f g := Room.hom_ext (funext (Sentence.map_comp f g)) (reductFunctor_comp f g)

def inst : Inst := ⟨Signature,institution⟩

end Silmaril.Logic.Separation.Parameterized
