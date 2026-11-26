module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

open CategoryTheory CategoryTheory.Limits PremonoidalCategory
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd)
open LambdaSSA.Semantics.Categorical
open LambdaSSA.Semantics.Categorical.SingletonDispatcher (route_inl route_inr caseWithContext_inr)
open LetIter.Semantics.Categorical (TypeModel InstructionModel retainEnvironment retainEnvironment_pre
  retainEnvironment_comp caseWithContext_project routeEnvironment contextualLoop_fixpoint
  extend_postmap case_return_map)
open LetIter.ProofRelevant.Semantics.Categorical (contextualLoop caseWithContext extend retainLeft)
open Silmaril.SSA.RVSDG.LambdaSSA.LinearChain (localSite)
open Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical (localInject)

local notation "bindArrow" => LetIter.ProofRelevant.Semantics.Categorical.bind

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v x y h k

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type x} {C : Type y} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  {d : Nat} {β : BoundCtx τ d} {L : LCtx τ} {n : Nat}

local notation "E" => ctxObj M β.toList

omit [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [TypeFormers τ]
  [InstructionModel J M Φ] in
@[reassoc] private theorem retain_postmap [DistributiveFreydCategory J] {D X Y Z : V}
    (pr : X ⟶ D) (f : J.obj X ⟶ J.obj Y) (g : Y ⟶ Z) :
    retainEnvironment J pr (f ≫ J.map g) = retainEnvironment J pr f ≫ J.map (D ◁ g) := by
  rw [retainEnvironment_comp]
  congr 1
  simp only [retainLeft, leftTensor, PremonoidalCategory.id_whiskerRight,
    Category.id_comp, Functor.StrongPremonoidal.tensor_naturality_right]
  simp

omit [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [TypeFormers τ]
  [InstructionModel J M Φ] in
@[reassoc] private theorem route_desc [DistributiveFreydCategory J] {D X Y Z : V}
    (l : X ⟶ Z) (r : Y ⟶ Z) {Q : C} (f : J.obj (D ⊗ Z) ⟶ Q) :
    routeEnvironment J D X Y ≫
      coprod.desc (J.map (D ◁ l) ≫ f) (J.map (D ◁ r) ≫ f) =
        J.map (D ◁ coprod.desc l r) ≫ f := by
  let inv := coprodComparison J (D ⊗ X) (D ⊗ Y) ≫
    J.map (DistributiveTensor.leftIso D X Y).hom
  let _ : Epi inv := by dsimp [inv]; infer_instance
  apply (cancel_epi inv).mp
  have cancel : inv ≫ routeEnvironment J D X Y = 𝟙 _ := by
    simp [inv, routeEnvironment, LetIter.ProofRelevant.Semantics.Categorical.splitMapCoprod, ← J.map_comp_assoc]
  rw [← Category.assoc, cancel, Category.id_comp]
  apply coprod.hom_ext
  · have leg : coprod.inl ≫ inv = J.map (D ◁ (coprod.inl : X ⟶ X ⨿ Y)) := by
      simp [inv, DistributiveTensor.leftIso, ← J.map_comp]
    rw [coprod.inl_desc, ← Category.assoc, leg, ← J.map_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp, coprod.inl_desc]
  · have leg : coprod.inr ≫ inv = J.map (D ◁ (coprod.inr : Y ⟶ X ⨿ Y)) := by
      simp [inv, DistributiveTensor.leftIso, ← J.map_comp]
    rw [coprod.inr_desc, ← Category.assoc, leg, ← J.map_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp, coprod.inr_desc]

private theorem dispatch_at (p : Table Φ β L n) (i : Fin (n + 1)) :
    J.map (E ◁ localInject M p.types i) ≫ p.dispatch J M = p.blockArrow J M i := by
  unfold Table.dispatch
  rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, localInject,
    labelObjToFinite_local M p.types i]
  simpa only [MonoidalCategory.id_tensorHom] using (p.collective_spec J M).restrict i

private theorem resultAt_boundary (p : Table Φ β L n) (i : Fin (n + 1)) :
    p.resultAt J M i =
      retainEnvironment J (fst E (M.obj (p.types i))) (p.blockArrow J M i) ≫ p.boundary J M := by
  let S := labelObj M (List.ofFn p.types)
  let T := labelObj M L
  have fst_snd : J.map (fst E S ▷ T) ≫ J.map (snd E T) = J.map (snd (E ⊗ S) T) := by
    rw [← J.map_comp, CartesianMonoidalCategory.whiskerRight_snd]
  have step : p.loop J M =
      retainEnvironment J (fst E S) (p.dispatch J M) ≫ p.boundary J M := by
    conv_lhs => rw [Table.loop, contextualLoop_fixpoint J]
    rw [← fst_snd, caseWithContext_project J (fst E S), retain_postmap_assoc]
    rfl
  rw [Table.resultAt, step, ← Category.assoc, retainEnvironment_pre J,
    CartesianMonoidalCategory.whiskerLeft_fst, dispatch_at]

private theorem target_boundary (p : Table Φ β L n) {A : τ} (t : Target p.types L A) :
    J.map (E ◁ labelInject M t.index t.typing) ≫ p.boundary J M = t.route J M p := by
  unfold Table.boundary
  rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp]
  cases t with
  | «local» i =>
    have split : labelInject M i (Target.local (L := L) i).typing ≫
        labelAppendSplit M (List.ofFn p.types) L = localInject M p.types i ≫ coprod.inr :=
      labelAppendSplit_local M p.types L i _ _
    simp only [Target.index]
    rw [split, MonoidalCategory.whiskerLeft_comp, J.map_comp_assoc,
      reassoc_of% (route_inr J), coprod.inr_desc]
    rfl
  | exit h =>
    simp only [Target.index]
    rw [labelAppendSplit_exit M p.types L h,
      MonoidalCategory.whiskerLeft_comp, J.map_comp_assoc, reassoc_of% (route_inl J), coprod.inl_desc,
      ← J.map_comp, CartesianMonoidalCategory.whiskerLeft_snd]
    rfl

variable [RegionTypingCoherent (Φ := Φ) J M]

theorem toSSA_denote_proof (p : Table Φ β L n) (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) :
    denoteRegion J M (p.toSSA_hasType i a) = bindArrow J (denoteOperand J M a) (p.resultAt J M i) := by
  let decl := denote_spec J M (Morphism.CaseSSA.erase_hasType a.2.toHasType)
  let he := p.entry_hasType i a
  have entry : RegionDenotes J M he (denoteOperand J M a ≫ J.map (labelInject M i (localSite p.types L i).typing)) :=
    RegionDenotes.br decl
  have native := RegionDenotes.cfg he (fun j => (p.block j).toSSA_hasType) entry
    (fun j => denoteRegion_spec J M _) (p.collective_spec J M)
  let split := labelAppendSplit M (List.ofFn p.types) L
  have step : contextualLoop J (J.map (E ◁ labelObjToFinite M p.types) ≫ p.collective J M ≫ J.map split) =
      p.loop J M := by simp only [Table.loop, Table.dispatch, Category.assoc, split]
  have leg : labelInject M i (localSite p.types L i).typing ≫ split =
      localInject M p.types i ≫ coprod.inr := labelAppendSplit_local M p.types L i _ _
  rw [← native.eq_denote, MonoidalCategory.id_tensorHom, step, Category.assoc, ← J.map_comp, leg,
    J.map_comp, ← Category.assoc, caseWithContext_inr J, extend_postmap, Category.assoc]
  rfl

variable [FreydCategory.CentralUnit J]

private theorem block_continued (p : Table Φ β L n) {A : τ}
    (b : Block Φ β p.types L A) :
    retainEnvironment J (fst E (M.obj A)) (denoteRegion J M b.toSSA_hasType) ≫ p.boundary J M =
      b.continued J M p := by
  cases b with
  | jump a t =>
    rw [← (RegionDenotes.br (h := t.typing)
      (denote_spec J M (Morphism.CaseSSA.erase_hasType a.2.toHasType))).eq_denote J M,
      retain_postmap_assoc, target_boundary]
    rfl
  | @case B D a l r =>
    let e := denoteOperand J M a ≫ J.map (M.coprodIso B D).hom
    let left := labelInject M l.index l.typing
    let right := labelInject M r.index r.typing
    have den := RegionDenotes.case (denote_spec J M (Morphism.CaseSSA.erase_hasType a.2.toHasType))
      (RegionDenotes.br (h := l.typing) (Denotes.var (J := J) (M := M) (i := 0) rfl))
      (RegionDenotes.br (h := r.typing) (Denotes.var (J := J) (M := M) (i := 0) rfl))
    have arrow : denoteRegion J M (Block.case a l r).toSSA_hasType = e ≫ J.map (coprod.desc left right) := by
      rw [← den.eq_denote]
      change caseWithContext J e (J.map (snd _ (M.obj B)) ≫ J.map left)
        (J.map (snd _ (M.obj D)) ≫ J.map right) = _
      rw [← J.map_comp, ← J.map_comp, case_return_map]
    rw [arrow, retain_postmap_assoc, Block.continued, caseWithContext_project]
    rw [← target_boundary J M p l, ← target_boundary J M p r, route_desc]

/-- One contextual unfolding retains the ambient variables and runs the
selected continuation after the current block. -/
theorem resultAt_step_proof (p : Table Φ β L n) (i : Fin (n + 1)) :
    p.resultAt J M i = (p.block i).continued J M p :=
  (resultAt_boundary J M p i).trans (block_continued J M p (p.block i))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
