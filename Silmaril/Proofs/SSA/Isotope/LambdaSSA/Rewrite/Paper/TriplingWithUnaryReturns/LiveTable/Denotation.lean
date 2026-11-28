module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable.Shape
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher
  (labelInject_payload payload_labelInject)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel retainEnvironment retainEnvironment_pre_assoc bind_retainEnvironment)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend splitMapCoprod)
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (entry_route local_route carryExit carryExit_typed orderedRow dispatcherRep packedReadbackRep)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd)

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

local notation "Ctx" => ctxObj M
local notation "Lbl" => labelObj M
local notation "Den" => denoteSingletonRegion J M
local notation "Reg" => denoteRegion J M

set_option backward.isDefEq.respectTransparency false

noncomputable def decodeStep (D P : τ) : M.obj (Silmaril.coprod D P) ⟶ Lbl [D] ⨿ M.obj P :=
  (M.coprodIso D P).hom ≫ coprod.map (labelInject M 0 rfl) (𝟙 _)

omit [FreydCategory.CentralUnit J] in
@[reassoc] private theorem decodeStep_image (D P : τ) :
    J.map (decodeStep M D P) ≫ splitMapCoprod J (Lbl [D]) (M.obj P) =
      J.map (M.coprodIso D P).hom ≫ splitMapCoprod J (M.obj D) (M.obj P) ≫
        coprod.map (J.map (labelInject M 0 (L := [D]) (A := D) rfl)) (𝟙 _) := by
  unfold decodeStep splitMapCoprod
  rw [J.map_comp, Category.assoc, coprodComparison_inv_natural, J.map_id]

omit [FreydCategory.CentralUnit J] in
@[reassoc] private theorem decodeExit_image (D P : τ) :
    J.map (decodeExit M D P) ≫ splitMapCoprod J (Lbl [D]) (M.obj P) =
      J.map (singletonLabelPayload M (Silmaril.coprod D P)) ≫ J.map (M.coprodIso D P).hom ≫
        splitMapCoprod J (M.obj D) (M.obj P) ≫
          coprod.map (J.map (labelInject M 0 (L := [D]) (A := D) rfl)) (𝟙 _) := by
  change J.map (singletonLabelPayload M (Silmaril.coprod D P) ≫ decodeStep M D P) ≫ _ = _
  rw [J.map_comp, Category.assoc, decodeStep_image]

include shared in
theorem denote_entry {n : Nat} (R : Fin n → τ) {X D : τ} {e : Region Φ}
    (he : ValueBranches [X] e (List.ofFn R ++ [D])) :
    let L := List.ofFn R
    let P := Silmaril.product X (packedExitType L)
    Reg (entry_route R he).hasType ≫ J.map (decodeExit M D P) =
      extend J (Reg he.hasType ≫ J.map (labelAppendSplit M L [D])) ≫
        J.map (carryRoute (capturedStateIso M X L).hom) := by
  dsimp only
  rw [stateIso_hom]
  simpa only [List.length_ofFn] using denote_carry J M shared R (rfl : At [X] 0 X) he

include shared in
theorem denote_row {n : Nat} (R : Fin n → τ) {X D : τ} {r : Fin n → Region Φ}
    (hr : ∀ i, ValueBranches [R i, X] (r i) (List.ofFn R ++ [D])) (i : Fin n) :
    let L := List.ofFn R
    let P := Silmaril.product X (packedExitType L)
    J.map (rowInputIso M X (R i)).hom ≫ Den (local_route R hr i).hasType ≫ J.map (decodeStep M D P) =
      retainEnvironment J (fst (Ctx [X]) (M.obj (R i)))
        (Reg (hr i).hasType ≫ J.map (labelAppendSplit M L [D])) ≫
          J.map (carryRoute (capturedStateIso M X L).hom) := by
  dsimp only
  let ht := (hr i).lsubst (carryExit_typed (Φ := Φ) (List.ofFn R) (rfl : At [R i, X] 1 X))
  have packed := denote_unpackBody J M shared ht
  simp only [List.length_ofFn] at packed
  have route := denote_carry J M shared R (rfl : At [R i, X] 1 X) (hr i)
  simp only [List.length_ofFn] at route
  rw [← Category.assoc, packed, Category.assoc, ← J.map_comp]
  change Reg _ ≫ J.map (decodeExit M D _) = _
  rw [route, ← row_capture, ← carryRoute_pre, J.map_comp]
  exact bind_retainEnvironment J _ _ _

omit [FreydCategory.CentralUnit J] in
private theorem contextual_label_ext {n : Nat} (R : Fin (n + 1) → τ) (Γ : VCtx τ)
    {Y : C} {f g : J.obj (Ctx Γ ⊗ Lbl (List.ofFn R)) ⟶ Y}
    (legs : ∀ i : Fin (n + 1), ∀ hi : At (List.ofFn R) i (R i),
      J.map (Ctx Γ ◁ labelInject M i hi) ≫ f = J.map (Ctx Γ ◁ labelInject M i hi) ≫ g) :
    f = g := by
  let p := (MonoidalCategory.tensorLeft (Ctx Γ)).mapIso (finiteLabelListIso M R)
  apply (cancel_epi (J.mapIso p).hom).mp
  apply collective_ext J M n Γ R
  intro i
  have hi : At (List.ofFn R) i (R i) := by
    simp only [At, List.getElem?_ofFn, dite_eq_left i.isLt]
  simp only [Functor.mapIso_hom, MonoidalCategory.id_tensorHom]
  change J.map (Ctx Γ ◁ finiteLabelInject M R i) ≫ J.map (Ctx Γ ◁ finiteLabelToList M R) ≫ f =
    J.map (Ctx Γ ◁ finiteLabelInject M R i) ≫ J.map (Ctx Γ ◁ finiteLabelToList M R) ≫ g
  rw [← J.map_comp_assoc, ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
    finiteLabelToList_leg M R i hi]
  exact legs i hi

include shared in
theorem denote_packed_table {n : Nat} (R : Fin (n + 1) → τ) {X D : τ}
    {e : Region Φ} {rows : Fin (n + 1) → Region Φ}
    (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (rows i) (List.ofFn R ++ [D]))
    (transport : ∀ {A P B : V} (p : A ≅ P)
      (f : J.obj A ⟶ J.obj B ⨿ J.obj A) (g : J.obj P ⟶ J.obj B ⨿ J.obj P),
      f ≫ coprod.map (𝟙 _) (J.map p.hom) = J.map p.hom ≫ g →
      iterate f = J.map p.hom ≫ iterate g) :
    Den (ValueBranches.cfg R he hb).hasType = Den (packedReadbackRep R he hb).property.hasType := by
  let L := List.ofFn R
  let P := Silmaril.product X (packedExitType L)
  let E := Ctx [X]
  let B := Lbl [D]
  let p := capturedStateIso M X L
  let splitter := labelAppendSplit M L [D]
  let entry := Reg he.hasType ≫ J.map splitter
  let frows := fun i => Reg (hb i).hasType
  obtain ⟨collective, hcollective⟩ := collectiveDenotes_exists_succ J M n [X] R [D] frows
  let body := J.map (E ◁ labelObjToFinite M R) ≫ collective ≫ J.map splitter
  let d := dispatcherRep X L (orderedRow R hb)
  let g := Den d.property.hasType ≫ J.map (decodeStep M D P) ≫ splitMapCoprod J B (M.obj P)
  have source := RegionDenotes.cfg (R := R) he.hasType (fun i => (hb i).hasType)
    (denoteRegion_spec J M he.hasType) (fun i => denoteRegion_spec J M (hb i).hasType) hcollective
  have square :
      retainEnvironment J (fst E (Lbl L)) body ≫ J.map (carryRoute p.hom) ≫ splitMapCoprod J B (M.obj P) =
        J.map p.hom ≫ g := by
    apply contextual_label_ext J M R [X]
    intro i hi
    let j : Fin L.length := ⟨i, by simp [L]⟩
    have hleg : J.map (E ◁ labelInject M i hi) ≫ body = frows i ≫ J.map splitter := by
      dsimp only [body]
      rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, labelObjToFinite_local M R i hi]
      rw [← Category.assoc, ← MonoidalCategory.id_tensorHom, hcollective.restrict]
    have pLeg : (E ◁ labelInject M i hi) ≫ p.hom =
        (E ◁ packedLabelInject M i hi) ≫ (rowInputIso M X (packedExitType L)).hom := by
      rw [stateIso_split]
      rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, labelInject_packLabel]
    have typedLeg :
        J.map (E ◁ packedLabelInject M i hi) ≫ J.map (rowInputIso M X (packedExitType L)).hom ≫
          Den d.property.hasType =
        J.map (rowInputIso M X (R i)).hom ≫ Den (local_route R hb i).hasType := by
      exact denote_dispatcher_leg_at J M shared X (Silmaril.coprod D P) L
        (orderedRow R hb) j hi (local_route R hb i) rfl
    rw [retainEnvironment_pre_assoc, CartesianMonoidalCategory.whiskerLeft_fst, hleg]
    dsimp only [g]
    rw [← J.map_comp_assoc, pLeg, J.map_comp, Category.assoc]
    have rowLeg := (congrArg (fun f => f ≫ J.map (decodeStep M D P) ≫ splitMapCoprod J B (M.obj P)) typedLeg).symm
    simp only [Category.assoc] at rowLeg
    rw [← rowLeg]
    have routed := congrArg (fun f => f ≫ splitMapCoprod J B (M.obj P))
      (denote_row J M shared R hb i)
    simp only [Category.assoc] at routed
    exact routed.symm
  have assembled := packed_dispatch_of_iterate J p entry body g square (fun {f} comm => transport p f g comm)
  have src :
      Reg (ValueBranches.cfg R he hb).hasType = extend J entry ≫ J.map (carryRoute p.hom) ≫
        splitMapCoprod J B (M.obj P) ≫ coprod.desc (𝟙 _) (iterate g) := by
    have h : Reg (ValueBranches.cfg R he hb).hasType = _ := (source.eq_denote J M).symm
    exact (by simpa only [entry, body, MonoidalCategory.id_tensorHom] using h :
      Reg (ValueBranches.cfg R he hb).hasType =
        Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.caseWithContext J entry
          (J.map (snd E B)) (Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.contextualLoop J body)).trans assembled
  have entryEq := denote_entry J M shared R he
  rw [← Category.assoc (extend J entry), ← entryEq] at src
  let idBranch : ValueBranches [D] (.br 0 (.var 0) : Region Φ) [D] := .br rfl (.var rfl)
  let loop := SyntacticCategory.iterateRegion_valueBranches d.property
  unfold denoteSingletonRegion
  rw [src]
  change _ = Den (CfgEta.TypeCategory.seqValueBranches (entry_route R he)
    (CfgEta.TypeCategory.caseValueBranches idBranch loop)).hasType
  rw [denote_seq J M shared (entry_route R he) (CfgEta.TypeCategory.caseValueBranches idBranch loop),
    denote_copair J M shared idBranch loop, denoteSingletonRegion_forward J M,
    denote_iterate J M shared d.property]
  let inject := J.map (labelInject M 0 (L := [D]) (A := D) rfl)
  let strip := J.map (singletonLabelPayload M D)
  let f := Den d.property.hasType ≫ J.map (M.coprodIso D P).hom ≫ splitMapCoprod J (M.obj D) (M.obj P)
  have inject_strip : inject ≫ strip = 𝟙 _ := by
    dsimp only [inject, strip]
    rw [← J.map_comp, labelInject_payload, J.map_id]
  have iterates : iterate g = iterate f ≫ inject := by
    have eq : g = f ≫ coprod.map inject (𝟙 _) := by
      dsimp only [g, f, inject]
      rw [decodeStep_image, Category.assoc, Category.assoc]
    rw [eq]
    exact (ElgotCategory.naturality f inject).symm
  have routes : coprod.map inject (𝟙 _) ≫ coprod.desc (𝟙 _) (iterate g) ≫ strip =
      coprod.desc (𝟙 _) (iterate f) := by
    apply coprod.hom_ext
    · rw [coprod.inl_map_assoc, coprod.inl_desc_assoc, Category.id_comp, inject_strip, coprod.inl_desc]
    · rw [coprod.inr_map_assoc, Category.id_comp, coprod.inr_desc_assoc, iterates,
        Category.assoc, inject_strip, Category.comp_id, coprod.inr_desc]
  simp only [denoteSingletonRegion, Category.assoc]
  erw [decodeExit_image_assoc J M D P]
  erw [routes]
  simp only [f, denoteSingletonRegion, Category.assoc, P, L]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable
