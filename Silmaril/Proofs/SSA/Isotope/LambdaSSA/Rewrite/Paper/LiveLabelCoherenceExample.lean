module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Freyd.Iteration.Coherence.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms

/-! # Live, differently typed label families with one common feedback state -/

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.LiveLabelFixture

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd toUnit)
open Semantics.Categorical
open SingletonDispatcher (cfgOne collectiveOne labelInject_payload payload_labelInject
  labelAppendSplit_zero labelAppendSplit_succ)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel case_pre_map case_postcomp)

private inductive Op where
  | poll

private abbrev U : Ty Empty := Silmaril.unit
private abbrev Flag : Ty Empty := Silmaril.coprod U U
private abbrev State (D : Ty Empty) := Silmaril.coprod U D

instance : HasTy Op (Ty Empty) where
  src _ := U
  trg _ := Flag

instance : HasEff Op Bool := ⟨fun _ => true⟩

private def entry : Region Op := .br 0 (.inl .unit)
private def block : Region Op :=
  .case (.op .poll (.var 1)) (.br 0 (.inl (.var 0))) (.br 1 (.var 0))

private def loop : Region Op := .cfg entry 1 (fun _ => block)

private theorem entryTyped (D : Ty Empty) : entry.HasType [U] [State D, U] :=
  .br rfl (.inl .unit)

private theorem blockTyped (D : Ty Empty) : block.HasType [State D, U] [State D, U] :=
  .case (.op (.var rfl)) (.br rfl (.inl (.var rfl))) (.br rfl (.var rfl))

private theorem loopTyped (D : Ty Empty) : loop.HasType [U] [U] :=
  .cfg (fun _ => State D) (entryTyped D) (fun _ => blockTyped D)

private def exitBlock : Region Op := .br 1 .unit

private def exitLoop : Region Op := .cfg entry 1 (fun _ => exitBlock)

private theorem exitBlockTyped (D : Ty Empty) : exitBlock.HasType [State D, U] [State D, U] :=
  .br rfl .unit

private theorem exitLoopTyped (D : Ty Empty) : exitLoop.HasType [U] [U] :=
  .cfg (fun _ => State D) (entryTyped D) (fun _ => exitBlockTyped D)

section Model

universe u₁ u₂ v₁ v₂
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

local notation "E" => ctxObj M [U]
local notation "UObj" => M.obj U
local notation "ExitObj" => labelObj M [U]
local notation "Small" => labelObj M [U]
local notation "Large" D => labelObj M [State D]

private noncomputable abbrev leftTag (D : Ty Empty) : UObj ⟶ M.obj (State D) :=
  coprod.inl ≫ (M.coprodIso U D).inv

private noncomputable abbrev emit : UObj ⟶ ExitObj := labelInject M 0 (L := [U]) rfl

private noncomputable def embed (D : Ty Empty) : Small ⟶ Large D :=
  singletonLabelPayload M U ≫ leftTag M D ≫ labelInject M 0 (L := [State D]) rfl

private noncomputable def requestStep {G X : V}
    (arg : G ⟶ UObj) (next : UObj ⟶ X) : J.obj G ⟶ J.obj (ExitObj ⨿ X) :=
  caseWithContext J (J.map arg ≫ InstructionModel.denote (J := J) (M := M) Op.poll ≫ J.map (M.coprodIso U U).hom)
    (J.map (snd G UObj ≫ next ≫ coprod.inr)) (J.map (snd G UObj ≫ emit M ≫ coprod.inl))

private theorem requestStep_pre {G H X : V} (h : H ⟶ G)
    (arg : G ⟶ UObj) (next : UObj ⟶ X) :
    J.map h ≫ requestStep J M arg next = requestStep J M (h ≫ arg) next := by
  unfold requestStep
  rw [← case_pre_map]
  simp only [← J.map_comp, CartesianMonoidalCategory.whiskerRight_snd_assoc]
  rw [← Category.assoc (J.map h), ← J.map_comp]

private theorem requestStep_post {G X Y : V} (h : X ⟶ Y)
    (arg : G ⟶ UObj) (next : UObj ⟶ X) :
    requestStep J M arg next ≫ J.map (coprod.map (𝟙 ExitObj) h) =
      requestStep J M arg (next ≫ h) := by
  unfold requestStep
  rw [case_postcomp]
  simp only [← J.map_comp, Category.assoc, coprod.inr_map, coprod.inl_map, Category.id_comp]

private noncomputable abbrev capture : E ⟶ UObj :=
  lookup M 0 (rfl : At [U] 0 U)

private noncomputable abbrev argument (T : V) : E ⊗ T ⟶ UObj :=
  fst E T ≫ capture M

private noncomputable def smallEntry : J.obj E ⟶ J.obj (ExitObj ⨿ Small) :=
  J.map (toUnit E ≫ M.unitIso.inv ≫ emit M ≫ coprod.inr)

private noncomputable def middle (D : Ty Empty) : J.obj (E ⊗ Large D) ⟶ J.obj (ExitObj ⨿ Small) :=
  requestStep J M (argument M (Large D)) (emit M)

private noncomputable def commonBody : J.obj (E ⊗ Small) ⟶ J.obj (ExitObj ⨿ Small) :=
  requestStep J M (argument M Small) (emit M)

private theorem before (D : Ty Empty) :
    J.map (E ◁ embed M D) ≫ middle J M D = commonBody J M := by
  unfold middle commonBody
  rw [requestStep_pre J M]
  unfold argument
  rw [CartesianMonoidalCategory.whiskerLeft_fst_assoc]

private noncomputable def largeEntry (D : Ty Empty) : J.obj E ⟶ J.obj (ExitObj ⨿ Large D) :=
  J.map (toUnit E ≫ M.unitIso.inv ≫ leftTag M D ≫ labelInject M 0 (L := [State D]) rfl ≫ coprod.inr)

omit [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [InstructionModel J M Op] in
private theorem entry_factor (D : Ty Empty) :
    smallEntry J M ≫ J.map (coprod.map (𝟙 ExitObj) (embed M D)) = largeEntry J M D := by
  unfold smallEntry largeEntry embed
  rw [← J.map_comp]
  congr 1
  rw [Category.assoc, Category.assoc, Category.assoc, coprod.inr_map, Category.assoc,
    ← Category.assoc (emit M), labelInject_payload M U, Category.id_comp, Category.assoc]

private noncomputable def largeBody (D : Ty Empty) : J.obj (E ⊗ Large D) ⟶ J.obj (ExitObj ⨿ Large D) :=
  requestStep J M (argument M (Large D)) (leftTag M D ≫ labelInject M 0 (L := [State D]) rfl)

private theorem body_factor (D : Ty Empty) :
    middle J M D ≫ J.map (coprod.map (𝟙 ExitObj) (embed M D)) = largeBody J M D := by
  unfold middle largeBody
  rw [requestStep_post J M, embed]
  have hp : emit M ≫ singletonLabelPayload M U = 𝟙 _ := labelInject_payload M U
  rw [← Category.assoc (emit M), hp, Category.id_comp]

private noncomputable def run (D : Ty Empty) : J.obj E ⟶ J.obj ExitObj :=
  caseWithContext J (largeEntry J M D) (J.map (snd E ExitObj)) (contextualLoop J (largeBody J M D))

private theorem compare (roll : IterationRolling C) (D : Ty Empty) :
    caseWithContext J (smallEntry J M) (J.map (snd E ExitObj)) (contextualLoop J (commonBody J M)) =
      run J M D := by
  have compared := cfgDispatch_of_state_factorization J roll
    (embed M D) (smallEntry J M) (middle J M D)
  rw [before J M, entry_factor J M, body_factor J M] at compared
  exact compared

private noncomputable def entryArrow (D : Ty Empty) :
    J.obj E ⟶ J.obj (labelObj M [State D, U]) :=
  J.map (toUnit E ≫ M.unitIso.inv ≫ leftTag M D ≫ labelInject M 0 rfl)

private theorem entry_denotes (D : Ty Empty) :
    RegionDenotes J M (entryTyped D) (entryArrow J M D) := by
  unfold entryArrow
  simp only [J.map_comp, Category.assoc]
  have d : Denotes J M (.unit (Γ := [U]) (Φ := Op))
      (J.map (toUnit E ≫ M.unitIso.inv)) := .unit
  have tagged := Denotes.inl (B := D) d
  have branch := RegionDenotes.br (h := (rfl : At [State D, U] 0 (State D))) tagged
  simpa only [entry, J.map_comp, Category.assoc] using branch

private noncomputable def blockArrow (D : Ty Empty) :
    J.obj (E ⊗ M.obj (State D)) ⟶ J.obj (labelObj M [State D, U]) :=
  let G := E ⊗ M.obj (State D)
  caseWithContext J
    (J.map (argument M (M.obj (State D))) ≫ InstructionModel.denote (J := J) (M := M) Op.poll ≫ J.map (M.coprodIso U U).hom)
    (J.map (snd G UObj ≫ leftTag M D ≫ labelInject M 0 rfl))
    (J.map (snd G UObj ≫ labelInject M 1 rfl))

private theorem block_denotes (D : Ty Empty) :
    RegionDenotes J M (blockTyped D) (blockArrow J M D) := by
  let a : At [State D, U] 1 U := rfl
  let b : At [U, State D, U] 0 U := rfl
  let again : At [State D, U] 0 (State D) := rfl
  let done : At [State D, U] 1 U := rfl
  have scrutinee :
      Denotes J M (.op (f := Op.poll) (.var a))
        (J.map (lookup M 1 a) ≫ InstructionModel.denote (J := J) (M := M) Op.poll) :=
    .op (.var a)
  have left :
      RegionDenotes J M (.br (Φ := Op) again (.inl (.var b)))
        ((J.map (lookup M 0 b) ≫ J.map (leftTag M D)) ≫ J.map (labelInject M 0 again)) :=
    .br (.inl (.var b))
  have right :
      RegionDenotes J M (.br (Φ := Op) done (.var b))
        (J.map (lookup M 0 b) ≫ J.map (labelInject M 1 done)) :=
    .br (.var b)
  have readCapture : lookup M 1 a = argument M (M.obj (State D)) := rfl
  have readReply : lookup M 0 b = snd (E ⊗ M.obj (State D)) UObj := rfl
  have d := RegionDenotes.case scrutinee left right
  rw [readCapture, readReply] at d
  erw [Category.assoc (J.map (argument M (M.obj (State D))))] at d
  unfold blockArrow
  simp only [block, argument, J.map_comp, Category.assoc] at d ⊢
  exact d

omit [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [InstructionModel J M Op] in
private theorem entry_cut (D : Ty Empty) :
    entryArrow J M D ≫ J.map (labelAppendSplit M [State D] [U]) = largeEntry J M D := by
  unfold entryArrow largeEntry
  rw [← J.map_comp, Category.assoc, Category.assoc, Category.assoc, labelAppendSplit_zero]

private theorem block_cut (D : Ty Empty) :
    J.map (E ◁ singletonLabelPayload M (State D)) ≫ blockArrow J M D ≫
      J.map (labelAppendSplit M [State D] [U]) = largeBody J M D := by
  have fromBlock : blockArrow J M D ≫ J.map (labelAppendSplit M [State D] [U]) =
      requestStep J M (argument M (M.obj (State D))) (leftTag M D ≫ labelInject M 0 rfl) := by
    unfold blockArrow requestStep
    rw [case_postcomp]
    simp only [← J.map_comp, Category.assoc, labelAppendSplit_zero,
      labelAppendSplit_succ M (State D) (rfl : At [U] 0 U)]
  rw [fromBlock, requestStep_pre J M]
  unfold largeBody argument
  rw [CartesianMonoidalCategory.whiskerLeft_fst_assoc]

private theorem run_denotes (D : Ty Empty) : RegionDenotes J M (loopTyped D) (run J M D) := by
  have d := cfgOne M J (entry_denotes J M D) (block_denotes J M D)
  rw [entry_cut J M D, block_cut J M D] at d
  exact d

private theorem entry_shape {S : Ty Empty} (h : entry.HasType [U] [S, U]) :
    ∃ D, S = State D := by
  unfold entry at h
  cases h with
  | br target term =>
      cases Option.some.inj target
      cases term with
      | inl ha =>
          cases ha
          exact ⟨_, rfl⟩

private theorem entry_determined (D : Ty Empty) :
    DeterminedRegion [U] entry [State D, U] :=
  .br rfl (.inl .unit)

private theorem block_determined (D : Ty Empty) :
    DeterminedRegion [State D, U] block [State D, U] :=
  .case (fun _ h => by cases h; rfl) (.op (.var rfl))
    (.br rfl (.inl (.var rfl))) (.br rfl (.var rfl))

/-- Every graph witness for this recurrent region has a label family selected
by the entry constructor. The tail is arbitrary. -/
private theorem run_all (roll : IterationRolling C)
    {t : loop.HasType [U] [U]} {f : J.obj E ⟶ J.obj ExitObj}
    (witness : RegionDenotes J M t f) :
    f = caseWithContext J (smallEntry J M) (J.map (snd E ExitObj))
      (contextualLoop J (commonBody J M)) := by
  unfold loop at witness
  cases witness with
  | cfg he hb de db dc =>
      rename_i R _ _ _
      have origin : entry.HasType [U] [R 0, U] := by
        simpa only [List.ofFn_succ, List.ofFn_zero, List.singleton_append] using he
      obtain ⟨D, shape⟩ := entry_shape origin
      have family : R = fun _ : Fin 1 => State D := by
        funext i
        exact Fin.cases shape (fun j => Fin.elim0 j) i
      subst R
      have entryEq := (entry_determined D).denotes_eq J M de (entry_denotes J M D)
      have bodyEq := (block_determined D).denotes_eq J M (db 0) (block_denotes J M D)
      have decode := collectiveOne M J dc
      erw [MonoidalCategory.id_tensorHom, ← Category.assoc (J.map (_ ◁ _)), decode,
        Category.assoc, entryEq, bodyEq, entry_cut J M D, block_cut J M D]
      exact (compare J M roll D).symm

private noncomputable def stopBody (S T : V) : J.obj (E ⊗ S) ⟶ J.obj (ExitObj ⨿ T) :=
  J.map (toUnit (E ⊗ S) ≫ M.unitIso.inv ≫ emit M ≫ coprod.inl)

/-- The original live ambiguity also factors through Unit. Its entry
enters the block, whose only transition goes to the outward label. -/
private theorem stop_denotes (roll : IterationRolling C) (D : Ty Empty) :
    RegionDenotes J M (exitLoopTyped D)
      (caseWithContext J (smallEntry J M) (J.map (snd E ExitObj))
        (contextualLoop J (stopBody J M Small Small))) := by
  let G := E ⊗ M.obj (State D)
  let goal : At [State D, U] 1 U := rfl
  have evalUnit : Denotes J M (.unit (Γ := [State D, U]) (Φ := Op))
      (J.map (toUnit G ≫ M.unitIso.inv)) := .unit
  have step : RegionDenotes J M (exitBlockTyped D)
      (J.map (toUnit G ≫ M.unitIso.inv) ≫ J.map (labelInject M 1 goal)) :=
    .br evalUnit
  have cfg := cfgOne M J (entry_denotes J M D) step
  have decode :
      J.map (E ◁ singletonLabelPayload M (State D)) ≫
        (J.map (toUnit G ≫ M.unitIso.inv) ≫ J.map (labelInject M 1 goal)) ≫
          J.map (labelAppendSplit M [State D] [U]) = stopBody J M (Large D) (Large D) := by
    unfold stopBody
    simp only [← J.map_comp, Category.assoc,
      labelAppendSplit_succ M (State D) (rfl : At [U] 0 U)]
    congr 1
    rw [← Category.assoc (E ◁ _), CartesianMonoidalCategory.comp_toUnit]
  have pre :
      J.map (E ◁ embed M D) ≫ stopBody J M (Large D) Small =
        stopBody J M Small Small := by
    unfold stopBody
    rw [← J.map_comp, ← Category.assoc (E ◁ _), CartesianMonoidalCategory.comp_toUnit]
  have post :
      stopBody J M (Large D) Small ≫ J.map (coprod.map (𝟙 ExitObj) (embed M D)) =
        stopBody J M (Large D) (Large D) := by
    unfold stopBody
    simp only [← J.map_comp, Category.assoc, coprod.inl_map, Category.id_comp]
  have factor := cfgDispatch_of_state_factorization J roll (embed M D)
    (smallEntry J M) (stopBody J M (Large D) Small)
  rw [pre, post, entry_factor J M D] at factor
  erw [entry_cut J M D, decode, ← factor] at cfg
  exact cfg

end Model

section BinaryFold

open Extension.Singleton
open Extension.Singleton.StructuralValues

local notation "Seed" => WithCaseReturns.BinaryFold.JoinedStep (τ := Ty Empty) (Φ := Op) true
local notation "inc" => inclusion Seed
local notation "model" => typeModel Seed

attribute [local instance] valueCartesian valueBraided computationPremonoidal computationSymmetric
  computationDistributive valueDistributive guardedIteration guardedElgot
attribute [local instance] Extension.Singleton.StructuralValues.hasFiniteCoproducts

private theorem rolling : IterationRolling (Extension.Singleton.TypeCategory Seed) :=
  fun h step => iterateChosen_roll Seed h step

/-- The actual graph witnesses use distinct singleton label families and the
same visible request on every round. The comparison uses chosen rolling. -/
example (uniform : StructuralUniformity Seed) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    letI := instructions Seed
    ∃ f,
      RegionDenotes inc model (loopTyped .empty) f ∧ RegionDenotes inc model (loopTyped U) f := by
  let strong := strongElgotOfStructuralUniformity Seed uniform
  let instr := instructions Seed
  have e := run_denotes inc model .empty
  have u := run_denotes inc model U
  have same := (compare inc model rolling .empty).symm.trans (compare inc model rolling U)
  exact ⟨_, e, same.symm ▸ u⟩

/-- The chosen arrow for the recurrent fixture agrees with every witness,
including every admissible tail type. -/
example (uniform : StructuralUniformity Seed) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    letI := instructions Seed
    ∀ {f}, RegionDenotes inc model (loopTyped .empty) f →
      f = denoteRegion inc model (loopTyped U) := by
  let strong := strongElgotOfStructuralUniformity Seed uniform
  let instr := instructions Seed
  intro f d
  exact (run_all inc model rolling d).trans
    (run_all inc model rolling (denoteRegion_spec inc model (loopTyped U))).symm

/-- The two original live label assignments give the same contextual graph arrow. -/
example (uniform : StructuralUniformity Seed) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    letI := instructions Seed
    ∃ f, RegionDenotes inc model (exitLoopTyped .empty) f ∧
      RegionDenotes inc model (exitLoopTyped U) f := by
  let strong := strongElgotOfStructuralUniformity Seed uniform
  let instr := instructions Seed
  exact ⟨_, stop_denotes inc model rolling .empty, stop_denotes inc model rolling U⟩

end BinaryFold

end Silmaril.Isotope.LambdaSSA.Region.Paper.LiveLabelFixture
