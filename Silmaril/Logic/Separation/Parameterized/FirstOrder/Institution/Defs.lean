module

public import Silmaril.Logic.Separation.Parameterized.FirstOrder.Transport.Defs

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.Parameterized.FirstOrder.Canonical
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
variable {A B C : Signature}

/-- Arbitrary native positive FO(LFP) formula pairs. Contexts, inner quantifiers
and recursive profiles need not be in the compiler image. No source syntax tag
or compiler-supplied semantic field is present. -/
structure FormulaPair (S : FOL.Signature) where
  contextSize : Nat
  profiles : Fin 0 → Silmaril.Logic.FirstOrderLFP.Profile S
  context : Fin contextSize → S.S
  pre : Silmaril.Logic.FirstOrderLFP.Formula S profiles context
  post : Silmaril.Logic.FirstOrderLFP.Formula S profiles context

abbrev Sentence (A : Signature) := FormulaPair (signature A)

def FormulaPair.map {S T : FOL.Signature} (f : S ⟶ T) (p : FormulaPair S) : FormulaPair T :=
  ⟨p.contextSize,fun i => (p.profiles i).map f,f.sorts ∘ p.context,p.pre.map f,p.post.map f⟩

def FormulaPair.Satisfies {S : FOL.Signature} (M : Silmaril.Logic.FirstOrderLFP.Model S)
    (p : FormulaPair S) : Prop :=
  p.pre.denote M (fun i => i.elim0) ⊆ p.post.denote M (fun i => i.elim0)

theorem FormulaPair.map_id {S : FOL.Signature} (p : FormulaPair S) : p.map (𝟙 S) = p := by
  cases p
  simp only [map,Silmaril.Logic.FirstOrderLFP.Formula.map_id]
  rfl

theorem FormulaPair.map_comp {S T U : FOL.Signature} (f : S ⟶ T) (g : T ⟶ U) (p : FormulaPair S) :
    p.map (f ≫ g) = (p.map f).map g := by
  cases p
  simp only [map,Silmaril.Logic.FirstOrderLFP.Formula.map_comp]
  rfl

theorem FormulaPair.satisfaction {S T : FOL.Signature} (f : S ⟶ T)
    (M : Silmaril.Logic.FirstOrderLFP.Model T) (p : FormulaPair S) :
    (p.map f).Satisfies M ↔ p.Satisfies ((Silmaril.Logic.FirstOrderLFP.reduct f).obj M) := by
  unfold Satisfies map
  rw [Silmaril.Logic.FirstOrderLFP.Formula.denote_map,Silmaril.Logic.FirstOrderLFP.Formula.denote_map]
  rfl

abbrev Sentence.map (f : A ⟶ B) (p : Sentence A) : Sentence B := FormulaPair.map (signatureMap f) p
abbrev Sentence.Satisfies (M : Model A) (p : Sentence A) : Prop := FormulaPair.Satisfies (model M) p

theorem Sentence.map_id (p : Sentence A) : Sentence.map (𝟙 A) p = p := by
  change FormulaPair.map (signatureMap (𝟙 A)) p = p
  rw [signatureMap_id]
  exact FormulaPair.map_id p

theorem Sentence.map_comp (f : A ⟶ B) (g : B ⟶ C) (p : Sentence A) :
    Sentence.map (f ≫ g) p = Sentence.map g (Sentence.map f p) := by
  change FormulaPair.map (signatureMap (f ≫ g)) p = _
  rw [signatureMap_comp,FormulaPair.map_comp]

theorem Sentence.satisfaction (f : A ⟶ B) (M : Model B) (p : Sentence A) :
    Sentence.Satisfies M (Sentence.map f p) ↔ Sentence.Satisfies (reduct f M) p := by
  change FormulaPair.Satisfies (model M) (FormulaPair.map (signatureMap f) p) ↔
    FormulaPair.Satisfies (model (reduct f M)) p
  rw [FormulaPair.satisfaction]
  exact Iff.of_eq (congrArg (fun N => FormulaPair.Satisfies N p) (model_reduct f M))

/-- Model arrows are every actual source value/resource homomorphism; their
ordinary FOL structure-hom laws are `FirstOrder.structureHom`. This institution
is a canonical-model entailment interface, separate from the existing FO(LFP)
and guarded-matching institutions whose model arrows are equality-only. -/
def institution : Signature ⥤ Room where
  obj A := ⟨Sentence A,Cat.of (Model A),Sentence.Satisfies⟩
  map f := ⟨Sentence.map f,reductFunctor f,Sentence.satisfaction f⟩
  map_id _ := Room.hom_ext (funext Sentence.map_id) reductFunctor_id
  map_comp f g := Room.hom_ext (funext (Sentence.map_comp f g)) (reductFunctor_comp f g)

def inst : Inst := ⟨Signature,institution⟩

end Silmaril.Logic.Separation.Parameterized.FirstOrder.Canonical
