module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable.Coordinates
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Dispatcher.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.CapturedSquare.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher
  (denote_weakenCapture route_inl route_inr)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel caseWithContext_project retainEnvironment_map routeEnvironment)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (splitMapCoprod)
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (dispatcherRep)
open Paper.RetainedLet (unpackBody unpackBody_typed)
open Paper.RetainedCase (boundCase boundCase_typed packedArms_typed routeCase_ofRegion
  routeCase_typed case_ofRegion_inl case_ofRegion_inr)
open Paper.PackedBody (applyPacked_typed unpack_applyPacked)
open Paper.TypeCategory (ofRegion ofType denoteFunctor denoteArrow_ofRegion sumCofanIsColimit sumCofan
  ofRegion_comp sumCofan_inl_sumIso_hom sumCofan_inr_sumIso_hom denoteExactSumIso denoteCoprodIso sumIso
  denoteFunctor_map_desc)
open CfgEta.TypeCategory (caseValueBranches seqValueBranches)
open CfgEta.TypeCategory.Retained (distributorRegion_typed)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd lift)

universe u v u₁ u₂ v₁ v₂
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ U W : V, ∃ h : J.obj U ⊗ J.obj W = J.obj (U ⊗ W),
    Functor.StrongPremonoidal.tensorIso (J := J) U W = eqToIso h)

local notation "Interp" => denoteFunctor (Φ := Φ) J M shared
local notation "Lit" => ofRegion (τ := τ) (Φ := Φ)
local notation "Den" => denoteSingletonRegion J M

set_option backward.isDefEq.respectTransparency false

include shared in
theorem denote_seq {A B D : τ} {l r : Region Φ}
    (hl : ValueBranches [A] l [B]) (hr : ValueBranches [B] r [D]) :
    Den (seqValueBranches hl hr).hasType = Den hl.hasType ≫ Den hr.hasType := by
  let F := Interp
  have h := congrArg (fun f => F.map f) (ofRegion_comp hl hr (seqValueBranches hl hr)).symm
  rw [F.map_comp] at h
  change Paper.TypeCategory.denoteArrow J M (Lit (seqValueBranches hl hr)) =
    Paper.TypeCategory.denoteArrow J M (Lit hl) ≫ Paper.TypeCategory.denoteArrow J M (Lit hr) at h
  simpa only [denoteArrow_ofRegion J M shared] using h

include shared in
theorem denote_unpackBody {X A D : τ} {r : Region Φ} (hr : ValueBranches [A, X] r [D]) :
    J.map (rowInputIso M X A).hom ≫ Den (unpackBody_typed hr).hasType =
      denoteRegion J M hr.hasType ≫ J.map (singletonLabelPayload M D) := by
  have apply := Paper.SingletonReification.denote_applyPacked J M (unpackBody_typed hr)
  have e := Paper.BoundSimulation.CapturedSquare.applyPacked_unpackBody hr
  have sound := e.sound J M shared (applyPacked_typed (unpackBody_typed hr)).hasType hr.hasType
  rw [sound] at apply
  exact apply.symm

omit [FreydCategory.CentralUnit J] in
private theorem denote_boundCase {Γ : VCtx τ} {A B D : τ} {l r : Region Φ}
    (hl : ValueBranches (A :: Γ) l [D]) (hr : ValueBranches (B :: Γ) r [D]) :
    denoteRegion J M (boundCase_typed hl hr).hasType =
      J.map (ctxObj M Γ ◁ (M.coprodIso A B).hom) ≫ routeEnvironment J (ctxObj M Γ) (M.obj A) (M.obj B) ≫
        coprod.desc (denoteRegion J M hl.hasType) (denoteRegion J M hr.hasType) := by
  let E := ctxObj M Γ
  let S := M.obj (Silmaril.coprod A B)
  let u := (M.coprodIso A B).hom
  have d := RegionDenotes.case
    (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (Γ := Silmaril.coprod A B :: Γ)
      (A := Silmaril.coprod A B) rfl)
    (denoteRegion_spec J M (hl.hasType.renameVars ((Ren.wk Γ (Silmaril.coprod A B)).lift A)))
    (denoteRegion_spec J M (hr.hasType.renameVars ((Ren.wk Γ (Silmaril.coprod A B)).lift B)))
  rw [← d.eq_denote J M, denote_weakenCapture M J hl.hasType,
    denote_weakenCapture M J hr.hasType]
  simp only [lookup, ← J.map_comp]
  rw [caseWithContext_project, retainEnvironment_map]
  have pair : lift (fst E S) (snd E S ≫ u) = E ◁ u := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [S]
  rw [pair]

include shared in
private theorem cons_dispatcher {X A D : τ} (L : LCtx τ)
    (rows : ∀ i : Fin (A :: L).length, {r : Region Φ // ValueBranches [Silmaril.product X ((A :: L).get i)] r [D]}) :
    let tail := (dispatcherRep X L (fun i => rows i.succ))
    J.map (rowInputIso M X (Silmaril.coprod A (packedExitType L))).hom ≫ Den (dispatcherRep X (A :: L) rows).property.hasType =
      J.map (ctxObj M [X] ◁ (M.coprodIso A (packedExitType L)).hom) ≫
        routeEnvironment J (ctxObj M [X]) (M.obj A) (M.obj (packedExitType L)) ≫
        coprod.desc (J.map (rowInputIso M X A).hom ≫ Den (rows 0).property.hasType)
          (J.map (rowInputIso M X (packedExitType L)).hom ≫ Den tail.property.hasType) := by
  dsimp only
  let hl : ValueBranches [Silmaril.product X A] (rows 0).val [D] := (rows 0).property
  let hr := (dispatcherRep X L (fun i => rows i.succ)).property
  let l := applyPacked_typed hl
  let r := applyPacked_typed hr
  have lEq : Lit (unpackBody_typed l) = Lit hl := (Paper.TypeCategory.ofRegion_eq_iff _ _).2 (unpack_applyPacked hl)
  have rEq : Lit (unpackBody_typed r) = Lit hr := (Paper.TypeCategory.ofRegion_eq_iff _ _).2 (unpack_applyPacked hr)
  have cases : Lit (caseValueBranches hl hr) = Lit (packedArms_typed l r) := by
    apply BinaryCofan.IsColimit.hom_ext
      (sumCofanIsColimit (Φ := Φ) (Silmaril.product X A) (Silmaril.product X (packedExitType L)))
    · rw [case_ofRegion_inl hl hr, case_ofRegion_inl (unpackBody_typed l) (unpackBody_typed r), lEq]
    · rw [case_ofRegion_inr hl hr, case_ofRegion_inr (unpackBody_typed l) (unpackBody_typed r), rEq]
  have rep : Lit (dispatcherRep X (A :: L) rows).property =
      Lit (unpackBody_typed (boundCase_typed l r)) := by
    let d := distributorRegion_typed (Φ := Φ) X A (packedExitType L)
    let c := caseValueBranches hl hr
    change Lit (seqValueBranches d c) = _
    rw [← ofRegion_comp d c (seqValueBranches d c), cases]
    exact routeCase_ofRegion l r
  have eq : Den (dispatcherRep X (A :: L) rows).property.hasType =
      Den (unpackBody_typed (boundCase_typed l r)).hasType := by
    have h := congrArg (fun f => (Interp).map f) rep
    change Paper.TypeCategory.denoteArrow J M _ = Paper.TypeCategory.denoteArrow J M _ at h
    simpa only [denoteArrow_ofRegion J M shared] using h
  rw [eq, denote_unpackBody J M shared (boundCase_typed l r), denote_boundCase J M l r]
  simp only [Category.assoc, coprod.desc_comp]
  rw [Paper.SingletonReification.denote_applyPacked J M hl, Paper.SingletonReification.denote_applyPacked J M hr]
  rfl

include shared in
theorem denote_dispatcher_leg (X D : τ) (L : LCtx τ)
    (rows : ∀ i : Fin L.length, {r : Region Φ // ValueBranches [Silmaril.product X (L.get i)] r [D]})
    (i : Fin L.length) :
    J.map (ctxObj M [X] ◁ packedLabelInject M i (labelAt_get L i)) ≫
      J.map (rowInputIso M X (packedExitType L)).hom ≫ Den (dispatcherRep X L rows).property.hasType =
    J.map (rowInputIso M X (L.get i)).hom ≫ Den (rows i).property.hasType := by
  induction L with
  | nil => exact i.elim0
  | cons A L ih =>
    let E := ctxObj M [X]
    let q := M.coprodIso A (packedExitType L)
    have dispatch := cons_dispatcher J M shared (X := X) (A := A) (D := D) L rows
    dsimp only at dispatch
    simp only [packedExitType] at *
    rw [dispatch]
    refine Fin.cases ?_ (fun j => ?_) i
    · have decode : (E ◁ packedLabelInject M (L := A :: L) 0 rfl) ≫ (E ◁ q.hom) =
          E ◁ (coprod.inl : M.obj A ⟶ M.obj A ⨿ M.obj (packedExitType L)) := by
        rw [← MonoidalCategory.whiskerLeft_comp]
        have tag : packedLabelInject M (L := A :: L) 0 rfl = coprod.inl ≫ q.inv := by
          simp [packedLabelInject, q]
        rw [tag, Category.assoc, q.inv_hom_id, Category.comp_id]
      rw [← J.map_comp_assoc]
      erw [decode]
      rw [← Category.assoc _ (routeEnvironment _ _ _ _), route_inl J, coprod.inl_desc]
      rfl
    · have decode : (E ◁ packedLabelInject M (L := A :: L) (j.succ : Fin (A :: L).length)
          (labelAt_get (A :: L) j.succ)) ≫ (E ◁ q.hom) =
          E ◁ (packedLabelInject M j (labelAt_get L j) ≫ coprod.inr) := by
        rw [← MonoidalCategory.whiskerLeft_comp]
        change E ◁ ((packedLabelInject M j (labelAt_get L j) ≫ coprod.inr ≫ q.inv) ≫ q.hom) = _
        simp
      rw [← J.map_comp_assoc]
      erw [decode]
      rw [MonoidalCategory.whiskerLeft_comp, J.map_comp, Category.assoc,
        ← Category.assoc _ (routeEnvironment _ _ _ _), route_inr J, coprod.inr_desc]
      exact ih (fun i => rows i.succ) j

include shared in
theorem denote_dispatcher_leg_at (X D : τ) (L : LCtx τ)
    (rows : ∀ i : Fin L.length, {r : Region Φ // ValueBranches [Silmaril.product X (L.get i)] r [D]})
    (i : Fin L.length) {A : τ} (hi : At L i A)
    {r : Region Φ} (hr : ValueBranches [Silmaril.product X A] r [D]) (row : (rows i).val = r) :
    J.map (ctxObj M [X] ◁ packedLabelInject M i hi) ≫
      J.map (rowInputIso M X (packedExitType L)).hom ≫ Den (dispatcherRep X L rows).property.hasType =
    J.map (rowInputIso M X A).hom ≫ Den hr.hasType := by
  have h : L.get i = A := Option.some.inj ((labelAt_get L i).symm.trans hi)
  subst A
  subst r
  exact denote_dispatcher_leg J M shared X D L rows i

include shared in
theorem denote_copair {A B D : τ} {l r : Region Φ}
    (hl : ValueBranches [A] l [D]) (hr : ValueBranches [B] r [D]) :
    Den (caseValueBranches hl hr).hasType =
      J.map (M.coprodIso A B).hom ≫ splitMapCoprod J (M.obj A) (M.obj B) ≫
        coprod.desc (Den hl.hasType) (Den hr.hasType) := by
  have src : Lit (caseValueBranches hl hr) = (sumIso A B).hom ≫ coprod.desc (Lit hl) (Lit hr) := by
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit (Φ := Φ) _ _)
    · rw [case_ofRegion_inl hl hr, ← Category.assoc, sumCofan_inl_sumIso_hom, coprod.inl_desc]
    · rw [case_ofRegion_inr hl hr, ← Category.assoc, sumCofan_inr_sumIso_hom, coprod.inr_desc]
  let F := Interp
  have h := congrArg (fun f => F.map f) src
  rw [F.map_comp, denoteFunctor_map_desc J M shared] at h
  simp only [denoteCoprodIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Category.assoc] at h
  rw [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp] at h
  change Paper.TypeCategory.denoteArrow J M _ = (denoteExactSumIso J M A B).hom ≫
    coprod.desc (Paper.TypeCategory.denoteArrow J M (Lit hl)) (Paper.TypeCategory.denoteArrow J M (Lit hr)) at h
  simpa only [denoteArrow_ofRegion J M shared, denoteExactSumIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_inv, splitMapCoprod, Category.assoc] using h

include shared in
theorem denote_iterate {A B : τ} {p : Region Φ}
    (hp : ValueBranches [A] p [Silmaril.coprod B A]) :
    Den (SyntacticCategory.iterateRegion_valueBranches hp).hasType =
      iterate (Den hp.hasType ≫ J.map (M.coprodIso B A).hom ≫ splitMapCoprod J (M.obj B) (M.obj A)) := by
  have h := Paper.TypeCategory.denoteFunctor_map_iterateSum J M shared (Lit hp)
  rw [Paper.TypeCategory.iterateSum_ofRegion] at h
  change Paper.TypeCategory.denoteArrow J M _ =
    iterate (Paper.TypeCategory.denoteArrow J M (Lit hp) ≫ (denoteExactSumIso J M B A).hom) at h
  simpa only [denoteArrow_ofRegion J M shared, denoteExactSumIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_inv, splitMapCoprod, Category.assoc] using h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable
