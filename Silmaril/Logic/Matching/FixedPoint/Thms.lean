module

public import Silmaril.Proofs.Logic.Matching.FixedPoint.Semantics

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.FixedPoint
open CategoryTheory Silmaril.Logic.Institution
open Algebraic.ManySorted (Signature)
variable {S : Type} {A B C : Signature S}

structure Sentence (A : Signature S) where
  setCount : Nat
  objectCount : Nat
  sets : Fin setCount → S
  objects : Fin objectCount → S
  sort : S
  pattern : Pattern A sets objects sort

def Sentence.map (f : A ⟶ B) (p : Sentence A) : Sentence B :=
  ⟨p.setCount, p.objectCount, p.sets, p.objects, p.sort, p.pattern.map f⟩
def Sentence.Satisfies (M : Model A) (p : Sentence A) : Prop :=
  ∀ (v : ObjEnv A M p.objects) (η : SetEnv A M p.sets) (x : M.carrier p.sort),
    x ∈ p.pattern.denote M v η

theorem Sentence.map_id (p : Sentence A) : p.map (𝟙 A) = p := by
  cases p
  exact congrArg (Sentence.mk _ _ _ _ _) (Pattern.map_id _)

theorem Sentence.map_comp (f : A ⟶ B) (g : B ⟶ C) (p : Sentence A) :
    p.map (f ≫ g) = (p.map f).map g := by
  cases p
  exact congrArg (Sentence.mk _ _ _ _ _) (Pattern.map_comp f g _)

def institution (S : Type) : Signature S ⥤ Room where
  obj A := ⟨Sentence A, Cat.of (Model A), Sentence.Satisfies⟩
  map f := ⟨Sentence.map f, FirstOrder.SignatureMap.reductFunctor f, by
    intro M p
    change (∀ v η x, x ∈ (p.pattern.map f).denote M v η) ↔
      ∀ v η x, x ∈ p.pattern.denote (FirstOrder.SignatureMap.reduct f M) v η
    simp only [Pattern.denote_map]
    rfl⟩
  map_id _ := Room.hom_ext (funext Sentence.map_id) FirstOrder.SignatureMap.reductFunctor_id
  map_comp f g := Room.hom_ext (funext (Sentence.map_comp f g))
    (FirstOrder.SignatureMap.reductFunctor_comp f g)

/-- The institution as a bundled `Inst`: its signatures and room functor `institution`, named so
that records and comorphisms can refer to it. -/
def inst (S : Type) := (⟨Signature S, institution S⟩ : Silmaril.Logic.Institution.Inst)

/-- Global inclusion preserves the original element context and global quantification. -/
def encodeFirstOrder (p : FirstOrder.Sentence A) : Sentence A :=
  ⟨0, p.variableCount, Fin.elim0, p.context, p.sort, .base p.pattern⟩

theorem firstOrder_satisfies (M : Model A) (p : FirstOrder.Sentence A) :
    Sentence.Satisfies M (encodeFirstOrder p) ↔ FirstOrder.Sentence.Satisfies M p := by
  constructor
  · intro h v x; exact h v (fun i => i.elim0) x
  · intro h v η x; exact h v x

def firstOrderNatural : FirstOrder.institution S ⟶ (𝟭 (Signature S)) ⋙ institution S where
  app A := ⟨encodeFirstOrder (A := A), 𝟭 (Model A), firstOrder_satisfies⟩
  naturality := by
    intro A B f
    exact Room.hom_ext (funext fun p => by cases p; rfl) rfl

def firstOrderToFixedPoint : Inst.CoHom ⟨Signature S, FirstOrder.institution S⟩
    ⟨Signature S, institution S⟩ := ⟨𝟭 _, firstOrderNatural⟩

theorem firstOrderToFixedPoint_modelExpansive :
    (firstOrderToFixedPoint (S := S)).ModelExpansive := fun _ M => ⟨M, rfl⟩

theorem firstOrder_entails_iff (A : Signature S) (H : Set (FirstOrder.Sentence A))
    (p : FirstOrder.Sentence A) :
    ((FirstOrder.institution S).obj A).Entails H p ↔
      ((institution S).obj A).Entails (encodeFirstOrder '' H) (encodeFirstOrder p) :=
  firstOrderToFixedPoint.entails_iff firstOrderToFixedPoint_modelExpansive A H p

/-- Equality-only pointed arrows permit the actual modal μ model reduct. -/
structure PointedModel (s : S) (A : Signature S) where
  base : Model A
  point : base.carrier s

instance (s : S) (A : Signature S) : Category (PointedModel s A) where
  Hom M N := PLift (M = N)
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

abbrev ClosedPattern (s : S) (A : Signature S) := Pattern A (r := 0) (k := 0) Fin.elim0 Fin.elim0 s

def PointedModel.Satisfies {s : S} (M : PointedModel s A) (p : ClosedPattern s A) : Prop :=
  M.point ∈ p.denote M.base (fun i => i.elim0) (fun i => i.elim0)

def pointedReduct {s : S} (f : A ⟶ B) (M : PointedModel s B) : PointedModel s A :=
  ⟨FirstOrder.SignatureMap.reduct f M.base, M.point⟩

def pointedReductFunctor {s : S} (f : A ⟶ B) : PointedModel s B ⥤ PointedModel s A where
  obj := pointedReduct f
  map h := ⟨congrArg (pointedReduct f) h.down⟩

theorem pointedReduct_id {s : S} (M : PointedModel s A) : pointedReduct (𝟙 A) M = M := by
  cases M with | mk base point => cases base; rfl

theorem pointedReductFunctor_id (s : S) (A : Signature S) :
    pointedReductFunctor (s := s) (𝟙 A) = 𝟭 (PointedModel s A) := by
  apply Functor.ext pointedReduct_id


theorem pointedReductFunctor_comp {s : S} (f : A ⟶ B) (g : B ⟶ C) :
    pointedReductFunctor (s := s) (f ≫ g) = pointedReductFunctor g ⋙ pointedReductFunctor f := rfl

def pointedInstitution (s : S) : Signature S ⥤ Room where
  obj A := ⟨ClosedPattern s A, Cat.of (PointedModel s A), PointedModel.Satisfies⟩
  map f := ⟨Pattern.map f, pointedReductFunctor f, by
    intro M p
    change M.point ∈ (p.map f).denote M.base _ _ ↔ _
    rw [Pattern.denote_map]
    rfl⟩
  map_id _ := Room.hom_ext (funext Pattern.map_id) (pointedReductFunctor_id _ _)
  map_comp f g := Room.hom_ext (funext (Pattern.map_comp f g)) (pointedReductFunctor_comp f g)

/-- The pointed institution as a bundled `Inst`, named so that records and comorphisms can refer
to it. -/
def pointedInst (s : S) := (⟨Signature S, pointedInstitution s⟩ : Silmaril.Logic.Institution.Inst)

def forgetFirstOrderPointed (s : S) (A : Signature S) :
    PointedModel s A ⥤ FirstOrder.Pointed.Model s A where
  obj M := ⟨M.base, M.point⟩
  map h := eqToHom (congrArg (fun M => FirstOrder.Pointed.Model.mk M.base M.point) h.down)
  map_id _ := rfl
  map_comp f g := by cases f.down; cases g.down; rfl

def firstOrderPointedNatural (s : S) : FirstOrder.Pointed.institution s ⟶
    (𝟭 (Signature S)) ⋙ pointedInstitution s where
  app A := ⟨Pattern.base, forgetFirstOrderPointed s A, fun _ _ => Iff.rfl⟩
  naturality := by
    intro A B f
    apply Room.hom_ext
    · funext p
      rfl
    · refine Functor.ext (fun _ => rfl) ?_
      intro M N h
      cases h.down
      rfl

def firstOrderPointedToFixedPoint (s : S) :
    Inst.CoHom ⟨Signature S, FirstOrder.Pointed.institution s⟩
      ⟨Signature S, pointedInstitution s⟩ := ⟨𝟭 _, firstOrderPointedNatural s⟩

theorem firstOrderPointedToFixedPoint_modelExpansive (s : S) :
    (firstOrderPointedToFixedPoint s).ModelExpansive :=
  fun _ M => ⟨⟨M.base, M.point⟩, by cases M; rfl⟩

theorem firstOrderPointed_entails_iff (s : S) (A : Signature S)
    (H : Set (FirstOrder.Pointed.ClosedPattern s A)) (p : FirstOrder.Pointed.ClosedPattern s A) :
    ((FirstOrder.Pointed.institution s).obj A).Entails H p ↔
      ((pointedInstitution s).obj A).Entails
        ((fun q => (Pattern.base q : ClosedPattern s A)) '' H) (.base p) :=
  (firstOrderPointedToFixedPoint s).entails_iff (firstOrderPointedToFixedPoint_modelExpansive s) A H p

def closedSentence {s : S} (p : ClosedPattern s A) : Sentence A :=
  ⟨0, 0, Fin.elim0, Fin.elim0, s, p⟩

theorem global_iff_all_points {s : S} (M : Model A) (p : ClosedPattern s A) :
    Sentence.Satisfies M (closedSentence p) ↔
      ∀ point : M.carrier s, (PointedModel.mk M point).Satisfies p := by
  constructor
  · intro h point; exact h (fun i => i.elim0) (fun i => i.elim0) point
  · intro h v η point
    have hv : v = (fun i => i.elim0) := funext fun i => i.elim0
    have hη : η = (fun i => i.elim0) := funext fun i => i.elim0
    cases hv; cases hη
    exact h point

end Silmaril.Logic.Matching.FixedPoint
