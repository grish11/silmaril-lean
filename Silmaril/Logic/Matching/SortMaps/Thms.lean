module

public import Silmaril.Proofs.Logic.Matching.SortMaps.Semantics

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.SortMaps
open CategoryTheory Silmaril.Logic.Institution
namespace Hom
variable {A B C : Signature}

private theorem hom_hext {M M' N N' : FirstOrder.Model A.symbols}
    (hM : M = M') (hN : N = N') (f : FirstOrder.Model.Hom M N)
    (g : FirstOrder.Model.Hom M' N') (h : HEq f.map g.map) : HEq f g := by
  cases hM; cases hN
  exact heq_of_eq (FirstOrder.Model.Hom.ext _ _ (eq_of_heq h))

theorem reductFunctor_id : reductFunctor (𝟙 A) = 𝟭 (FirstOrder.Model A.symbols) := by
  apply Functor.hext reduct_id
  intro M N f
  exact hom_hext (reduct_id M) (reduct_id N) _ _ HEq.rfl

theorem reductFunctor_comp (f : A ⟶ B) (g : B ⟶ C) :
    reductFunctor (f ≫ g) = reductFunctor g ⋙ reductFunctor f := rfl

@[simp] theorem sentence_id (p : FirstOrder.Sentence A.symbols) : sentence (𝟙 A) p = p := by
  cases p
  exact congrArg (FirstOrder.Sentence.mk _ _ _) (pattern_id _)

@[simp] theorem sentence_comp (f : A ⟶ B) (g : B ⟶ C) (p : FirstOrder.Sentence A.symbols) :
    sentence (f ≫ g) p = sentence g (sentence f p) := by
  cases p
  exact congrArg (FirstOrder.Sentence.mk _ _ _) (pattern_comp f g _)
end Hom

/-- First-order matching over signatures whose sort sets may vary. -/
def institution : Signature ⥤ Room where
  obj A := ⟨FirstOrder.Sentence A.symbols, Cat.of (FirstOrder.Model A.symbols), FirstOrder.Sentence.Satisfies⟩
  map f := ⟨Hom.sentence f, Hom.reductFunctor f, Hom.satisfaction f⟩
  map_id _ := Room.hom_ext (funext Hom.sentence_id) Hom.reductFunctor_id
  map_comp f g := Room.hom_ext (funext (Hom.sentence_comp f g)) (Hom.reductFunctor_comp f g)

/-- `institution` as a bundled `Inst`, named so that records and comorphisms can refer to it. -/
def inst := (⟨Signature, institution⟩ : Silmaril.Logic.Institution.Inst)
end Silmaril.Logic.Matching.SortMaps

@[expose] public section
namespace Silmaril.Logic.Matching.SortMaps
open CategoryTheory Silmaril.Logic.Institution
namespace Hom
variable {A B C : Signature}
@[simp] theorem fixedSentence_id (p : FixedPoint.Sentence A.symbols) : fixedSentence (𝟙 A) p = p := by
  cases p
  exact congrArg (FixedPoint.Sentence.mk _ _ _ _ _) (fixedPattern_id _)

@[simp] theorem fixedSentence_comp (f : A ⟶ B) (g : B ⟶ C) (p : FixedPoint.Sentence A.symbols) :
    fixedSentence (f ≫ g) p = fixedSentence g (fixedSentence f p) := by
  cases p
  exact congrArg (FixedPoint.Sentence.mk _ _ _ _ _) (fixedPattern_comp f g _)

theorem fixedSatisfaction (f : A ⟶ B) (M : FirstOrder.Model B.symbols)
    (p : FixedPoint.Sentence A.symbols) :
    FixedPoint.Sentence.Satisfies M (fixedSentence f p) ↔
      FixedPoint.Sentence.Satisfies (reduct f M) p := by
  change (∀ v η x, x ∈ (fixedPattern f p.pattern).denote M v η) ↔ _
  simp only [denote_fixedPattern]
  rfl
end Hom

/-- Full native matching μ/ν institution with varying sort sets. -/
def fixedInstitution : Signature ⥤ Room where
  obj A := ⟨FixedPoint.Sentence A.symbols, Cat.of (FirstOrder.Model A.symbols), FixedPoint.Sentence.Satisfies⟩
  map f := ⟨Hom.fixedSentence f, Hom.reductFunctor f, Hom.fixedSatisfaction f⟩
  map_id _ := Room.hom_ext (funext Hom.fixedSentence_id) Hom.reductFunctor_id
  map_comp f g := Room.hom_ext (funext (Hom.fixedSentence_comp f g)) (Hom.reductFunctor_comp f g)

/-- `fixedInstitution` as a bundled `Inst`, named so that records and comorphisms can refer to it. -/
def fixedInst := (⟨Signature, fixedInstitution⟩ : Silmaril.Logic.Institution.Inst)

/-- The old fixed-sort signature category embeds without changing models. -/
def fixedSortSignatures (S : Type) : SortedSignature S ⥤ Signature where
  obj A := ⟨S, A⟩
  map f := ⟨id, fun op => f.operations op⟩

theorem fixedSort_pattern {S : Type} {A B : SortedSignature S} (f : A ⟶ B)
    {k : Nat} {Γ : Fin k → S} {s : S} (p : FirstOrder.Pattern A Γ s) :
    Hom.pattern ((fixedSortSignatures S).map f) p = FirstOrder.Pattern.map f p := by
  induction p with
  | var => rfl
  | app op args ih => exact congrArg (FirstOrder.Pattern.app _) (funext ih)
  | neg p ih => exact congrArg FirstOrder.Pattern.neg ih
  | conj p q hp hq => exact congrArg₂ FirstOrder.Pattern.conj hp hq
  | ex bound p hp =>
      change FirstOrder.Pattern.ex bound _ = FirstOrder.Pattern.ex bound _
      exact congrArg (FirstOrder.Pattern.ex bound) hp

/-- No syntax or model changes are hidden in the fixed-sort inclusion. -/
def fixedSortFirstOrder (S : Type) : FirstOrder.institution S ⟶ fixedSortSignatures S ⋙ institution where
  app A := ⟨id, 𝟭 _, fun _ _ => Iff.rfl⟩
  naturality := by
    intro A B f
    apply Room.hom_ext
    · funext p
      change FirstOrder.Sentence.map f p = Hom.sentence ((fixedSortSignatures S).map f) p
      cases p with
      | mk k Γ s p => exact congrArg (FirstOrder.Sentence.mk k Γ s) (fixedSort_pattern f p).symm
    · rfl
end Silmaril.Logic.Matching.SortMaps

@[expose] public section
namespace Silmaril.Logic.Matching.SortMaps
open CategoryTheory Silmaril.Logic.Institution

theorem fixedSort_fixedPattern {S : Type} {A B : SortedSignature S} (f : A ⟶ B)
    {r k : Nat} {P : Fin r → S} {Γ : Fin k → S} {s : S}
    (p : FixedPoint.Pattern A P Γ s) :
    Hom.fixedPattern ((fixedSortSignatures S).map f) p = FixedPoint.Pattern.map f p := by
  induction p with
  | base p => exact congrArg FixedPoint.Pattern.base (fixedSort_pattern f p)
  | setvar => rfl
  | app op args ih => exact congrArg (FixedPoint.Pattern.app _) (funext ih)
  | dualApp op args ih => exact congrArg (FixedPoint.Pattern.dualApp _) (funext ih)
  | conj p q hp hq => exact congrArg₂ FixedPoint.Pattern.conj hp hq
  | disj p q hp hq => exact congrArg₂ FixedPoint.Pattern.disj hp hq
  | ex bound p hp =>
      change FixedPoint.Pattern.ex bound _ = FixedPoint.Pattern.ex bound _
      exact congrArg (FixedPoint.Pattern.ex bound) hp
  | all bound p hp =>
      change FixedPoint.Pattern.all bound _ = FixedPoint.Pattern.all bound _
      exact congrArg (FixedPoint.Pattern.all bound) hp
  | mu p hp => exact congrArg FixedPoint.Pattern.mu hp
  | nu p hp => exact congrArg FixedPoint.Pattern.nu hp

def fixedSortFixedPoint (S : Type) : FixedPoint.institution S ⟶
    fixedSortSignatures S ⋙ fixedInstitution where
  app A := ⟨id, 𝟭 _, fun _ _ => Iff.rfl⟩
  naturality := by
    intro A B f
    apply Room.hom_ext
    · funext p
      change FixedPoint.Sentence.map f p = Hom.fixedSentence ((fixedSortSignatures S).map f) p
      cases p with
      | mk r k P Γ s p => exact congrArg (FixedPoint.Sentence.mk r k P Γ s) (fixedSort_fixedPattern f p).symm
    · rfl

private theorem base_heq {S : Type} {A : SortedSignature S} {r k : Nat}
    {P Q : Fin r → S} {Γ : Fin k → S} {s : S} (h : P = Q) (p : FirstOrder.Pattern A Γ s) :
    HEq (FixedPoint.Pattern.base (P := P) p) (FixedPoint.Pattern.base (P := Q) p) := by
  cases h
  rfl

/-- First-order encoding commutes with arbitrary sort and operation maps. -/
theorem Hom.encodeFirstOrder_map {A B : Signature} (f : A ⟶ B)
    (p : FirstOrder.Sentence A.symbols) :
    Hom.fixedSentence f (FixedPoint.encodeFirstOrder p) =
      FixedPoint.encodeFirstOrder (Hom.sentence f p) := by
  symm
  have hsets : f.sorts ∘ (Fin.elim0 : Fin 0 → A.sorts) = Fin.elim0 := funext (fun i => i.elim0)
  cases p
  simp only [Hom.sentence, Hom.fixedSentence, FixedPoint.encodeFirstOrder, Hom.fixedPattern]
  congr 1
  · exact hsets.symm
  · exact base_heq hsets.symm _

/-- Existing first-order inclusion is natural also for changing sort sets. -/
def firstOrderNatural : institution ⟶ (𝟭 Signature) ⋙ fixedInstitution where
  app A := ⟨FixedPoint.encodeFirstOrder, 𝟭 _, FixedPoint.firstOrder_satisfies⟩
  naturality := by
    intro A B f
    apply Room.hom_ext
    · funext p
      exact (Hom.encodeFirstOrder_map f p).symm
    · rfl

def firstOrderToFixedPoint : Inst.CoHom ⟨Signature, institution⟩ ⟨Signature, fixedInstitution⟩ :=
  ⟨𝟭 _, firstOrderNatural⟩

theorem firstOrderToFixedPoint_modelExpansive : firstOrderToFixedPoint.ModelExpansive :=
  fun _ M => ⟨M, rfl⟩
end Silmaril.Logic.Matching.SortMaps
