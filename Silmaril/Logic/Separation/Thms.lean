module

public import Silmaril.Logic.Separation.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation
open CategoryTheory Silmaril.Logic.Institution
variable {A B C : Signature}

@[simp] theorem Assertion.map_id (p : Assertion A) : p.map (𝟙 A) = p := by
  induction p <;> simp_all only [map, CategoryStruct.id]
  rfl

@[simp] theorem Assertion.map_comp (f : A ⟶ B) (g : B ⟶ C) (p : Assertion A) :
    p.map (f ≫ g) = (p.map f).map g := by
  induction p <;> simp_all only [map, CategoryStruct.comp, Function.comp_apply]

theorem Assertion.denote_map (f : A ⟶ B) (M : Model B) (p : Assertion A) :
    (p.map f).denote M = p.denote (reduct f M) := by
  induction p with
  | atom => rfl
  | emp => rfl
  | neg p ih => exact congrArg Set.compl ih
  | conj p q hp hq => exact congrArg₂ Set.inter hp hq
  | sep p q hp hq => exact congrArg₂ M.resource.sep hp hq
  | wand p q hp hq => exact congrArg₂ M.resource.wand hp hq

@[simp] theorem Pattern.map_id {r} (p : Pattern A r) : p.map (𝟙 A) = p := by
  induction p <;> simp_all only [map, Assertion.map_id]

@[simp] theorem Pattern.map_comp (f : A ⟶ B) (g : B ⟶ C) {r} (p : Pattern A r) :
    p.map (f ≫ g) = (p.map f).map g := by
  induction p <;> simp_all only [map, Assertion.map_comp]

theorem Pattern.denote_map (f : A ⟶ B) (M : Model B) {r} (p : Pattern A r) :
    (p.map f).denote M = p.denote (reduct f M) := by
  induction p with
  | base p => exact OrderHom.ext _ _ (funext fun _ => p.denote_map f M)
  | var => rfl
  | conj p q hp hq => exact OrderHom.ext _ _ (funext fun η => congrArg₂ Set.inter (congrArg (fun F => F η) hp) (congrArg (fun F => F η) hq))
  | disj p q hp hq => exact OrderHom.ext _ _ (funext fun η => congrArg₂ Set.union (congrArg (fun F => F η) hp) (congrArg (fun F => F η) hq))
  | sep p q hp hq => exact OrderHom.ext _ _ (funext fun η => congrArg₂ M.resource.sep (congrArg (fun F => F η) hp) (congrArg (fun F => F η) hq))
  | wand p q hq => exact OrderHom.ext _ _ (funext fun η => congrArg₂ M.resource.wand (p.denote_map f M) (congrArg (fun F => F η) hq))
  | mu p hp =>
      apply OrderHom.ext
      funext η
      apply congrArg OrderHom.lfp
      apply OrderHom.ext
      funext X
      exact congrArg (fun F => F (Fin.cases X η)) hp

structure BaseSentence (A : Signature) where
  pre : Assertion A
  post : Assertion A

def BaseSentence.map (f : A ⟶ B) (p : BaseSentence A) : BaseSentence B := ⟨p.pre.map f, p.post.map f⟩
def BaseSentence.Satisfies (M : Model A) (p : BaseSentence A) : Prop := p.pre.denote M ⊆ p.post.denote M

structure Sentence (A : Signature) where
  pre : Pattern A 0
  post : Pattern A 0

def Sentence.map (f : A ⟶ B) (p : Sentence A) : Sentence B := ⟨p.pre.map f, p.post.map f⟩
def Sentence.Satisfies (M : Model A) (p : Sentence A) : Prop :=
  p.pre.denote M (fun i => i.elim0) ⊆ p.post.denote M (fun i => i.elim0)

@[simp] theorem BaseSentence.map_id (p : BaseSentence A) : p.map (𝟙 A) = p := by cases p; simp [map]
@[simp] theorem BaseSentence.map_comp (f : A ⟶ B) (g : B ⟶ C) (p : BaseSentence A) :
    p.map (f ≫ g) = (p.map f).map g := by cases p; simp [map]

theorem BaseSentence.satisfaction (f : A ⟶ B) (M : Model B) (p : BaseSentence A) :
    (p.map f).Satisfies M ↔ p.Satisfies (reduct f M) := by
  simp only [Satisfies, map, Assertion.denote_map]
  rfl

@[simp] theorem Sentence.map_id (p : Sentence A) : p.map (𝟙 A) = p := by cases p; simp [map]
@[simp] theorem Sentence.map_comp (f : A ⟶ B) (g : B ⟶ C) (p : Sentence A) :
    p.map (f ≫ g) = (p.map f).map g := by cases p; simp [map]

theorem Sentence.satisfaction (f : A ⟶ B) (M : Model B) (p : Sentence A) :
    (p.map f).Satisfies M ↔ p.Satisfies (reduct f M) := by
  simp only [Satisfies, map, Pattern.denote_map]
  rfl

def baseInstitution : Signature ⥤ Room where
  obj A := ⟨BaseSentence A, Cat.of (Model A), BaseSentence.Satisfies⟩
  map f := ⟨BaseSentence.map f, reductFunctor f, BaseSentence.satisfaction f⟩
  map_id _ := Room.hom_ext (funext BaseSentence.map_id) reductFunctor_id
  map_comp f g := Room.hom_ext (funext (BaseSentence.map_comp f g)) (reductFunctor_comp f g)

def institution : Signature ⥤ Room where
  obj A := ⟨Sentence A, Cat.of (Model A), Sentence.Satisfies⟩
  map f := ⟨Sentence.map f, reductFunctor f, Sentence.satisfaction f⟩
  map_id _ := Room.hom_ext (funext Sentence.map_id) reductFunctor_id
  map_comp f g := Room.hom_ext (funext (Sentence.map_comp f g)) (reductFunctor_comp f g)

def ofBase (p : BaseSentence A) : Sentence A := ⟨.base p.pre, .base p.post⟩

def baseToRecursiveNat : baseInstitution ⟶ institution where
  app _ := ⟨ofBase, 𝟭 _, fun _ _ => Iff.rfl⟩
  naturality := by intro A B f; apply Room.hom_ext <;> rfl

def baseInst : Inst := ⟨Signature, baseInstitution⟩
def recursiveInst : Inst := ⟨Signature, institution⟩
def baseToRecursive : Inst.CoHom baseInst recursiveInst where
  Φ := 𝟭 _
  ρ := baseToRecursiveNat ≫ (Functor.leftUnitor institution).inv

theorem baseToRecursive_modelExpansive : baseToRecursive.ModelExpansive := fun _ M => ⟨M, rfl⟩

theorem baseToRecursive_entails_iff (A : Signature) (H : Set (BaseSentence A)) (p : BaseSentence A) :
    (baseInstitution.obj A).Entails H p ↔ (institution.obj A).Entails (ofBase '' H) (ofBase p) :=
  baseToRecursive.entails_iff baseToRecursive_modelExpansive A H p

end Silmaril.Logic.Separation
