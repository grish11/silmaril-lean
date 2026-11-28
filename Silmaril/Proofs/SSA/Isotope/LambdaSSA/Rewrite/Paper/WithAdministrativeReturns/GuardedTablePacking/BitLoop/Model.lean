module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Preservation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

/-! # The literal loop in ordered-trace Kleisli models

The first part holds for every coherent instruction interpretation on the
ordered-trace Kleisli category. The last part fixes the four-reply model.
-/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithAdministrativeReturns
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature Exits model Trace modelCoherent)
open Paper.WithCaseBind.BitQuery.RequestTree
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Paper.Extension.Singleton (ofRegion ofType projection iterateSum iterateSum_map)
open Paper.Extension.Singleton.Generation
open Silmaril.Semantics.NondeterministicTrace (Tagged Finite)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types
local notation "T" => Coordinates.ofModel (τ := Ty Empty) J M
local notation "N" => WithGuardedTablePacking.Step (τ := Ty Empty) (Φ := signature.Instr) false

set_option backward.isDefEq.respectTransparency false in
theorem sumIso_coprodIsoSum (A B : Ty Empty) :
    ((T).sumIso A B).hom ≫
      (Kleisli.Type.coprodIsoSum Trace ((J).obj ((M).obj A)) ((J).obj ((M).obj B))).hom =
        𝟙 ((J).obj ((M).obj (Silmaril.coprod A B))) := by
  let typeSum := Types.binaryCoproductIso ((M).obj A) ((M).obj B)
  have chosen :
      (PreservesColimitPair.iso (J) ((M).obj A) ((M).obj B)).hom ≫ (J).map typeSum.hom =
        (Kleisli.Type.coprodIsoSum Trace ((J).obj ((M).obj A)) ((J).obj ((M).obj B))).hom := by
    rw [PreservesColimitPair.iso_hom]
    apply coprod.hom_ext
    · simp only [coprodComparison, coprod.inl_desc_assoc,
        Kleisli.Type.inl_coprodIsoSum_hom, ← Functor.map_comp, typeSum]
      rw [Types.binaryCoproductIso_inl_comp_hom]
      rfl
    · simp only [coprodComparison, coprod.inr_desc_assoc,
        Kleisli.Type.inr_coprodIsoSum_hom, ← Functor.map_comp, typeSum]
      rw [Types.binaryCoproductIso_inr_comp_hom]
      rfl
  have decoded : ((M).coprodIso A B).hom ≫ typeSum.hom = 𝟙 _ := by
    change (_ ≫ typeSum.inv) ≫ typeSum.hom = 𝟙 _
    rw [Category.assoc, Iso.inv_hom_id]
    rfl
  simp only [Coordinates.ofModel, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [(Iso.inv_comp_eq _).2 chosen.symm, ← Functor.map_comp, decoded]
  exact (J).map_id _

set_option backward.isDefEq.respectTransparency false in
private theorem packedInject_apply (x : value Bit) :
    (packedLabelInject M 0 (rfl : At [Bit] 0 Bit)) x = (Sum.inl x : value State) := by
  simp only [packedLabelInject, eqToHom_refl, Category.id_comp]
  exact ConcreteCategory.congr_hom (Types.binaryCoproductIso_inl_comp_hom
    (value Bit) (value (packedExitType ([] : LCtx (Ty Empty))))) x

theorem stepArrow_eq (p : Program) :
    stepArrow p = ofRegion N unpack_typed ≫ ofRegion N p.typed.packExits :=
  (congrArg (projection N).map
    (Paper.TypeCategory.ofRegion_comp unpack_typed p.typed.packExits (step_typed p))).symm.trans
    ((projection N).map_comp _ _)

theorem loopArrow_eq (p : Program) : loopArrow p = iterateSum N (stepArrow p) :=
  ((iterateSum_map N (Paper.TypeCategory.ofRegion (step_typed p))).trans
    (congrArg (projection N).map (Paper.TypeCategory.iterateSum_ofRegion (step_typed p)))).symm

section Coherent

-- The instruction interpretation is the parameter of this section.
set_option linter.concreteInstances false

variable [inst : InstructionModel J M signature.Instr] [RegionTypingCoherent (Φ := signature.Instr) J M]

/-- The quotient's interpretation in a coherent trace model. -/
noncomputable abbrev F :=
  WithGuardedTablePacking.denoteFunctor (Φ := signature.Instr) false J M (fun _ _ => ⟨rfl, rfl⟩)

/-- The step of a program at the exact packed representative. -/
@[expose] noncomputable def stepIn (p : Program) : value State → Trace (value Bit ⊕ value State) :=
  fun s => (denoteSingletonRegion J M p.typed.packExits.hasType).of (Sum.elim id PEmpty.elim s)

set_option backward.isDefEq.respectTransparency false in
/-- Guarded feedback of the quotient is the model's iterator on values. -/
theorem map_iterateSum_of {A B : Ty Empty} (s : ofType N A ⟶ ofType N (Silmaril.coprod B A))
    (a : value A) :
    ((F).map (iterateSum N s)).of a =
      Silmaril.Elgot.iter (m := Trace)
        (fun x : value A => (((F).map s).of x : Trace (value B ⊕ value A))) a := by
  let step : (J).obj ((M).obj A) ⟶ (J).obj ((M).obj (Silmaril.coprod B A)) := (F).map s
  have preserved : (F).map (iterateSum N s) = CategoryTheory.iterate (step ≫ ((T).sumIso B A).hom) :=
    Paper.Extension.Singleton.denoteFunctor_map_iterateSum J M (fun _ _ => ⟨rfl, rfl⟩)
      (WithGuardedTablePacking.seedDenotes false J M (fun _ _ => ⟨rfl, rfl⟩)) s
  calc
    _ = (CategoryTheory.iterate (step ≫ ((T).sumIso B A).hom)).of a :=
      congrArg (fun g : (J).obj ((M).obj A) ⟶ (J).obj ((M).obj B) => g.of a) preserved
    _ = _ := by
      rw [Kleisli.Type.iterate_of, Category.assoc, sumIso_coprodIsoSum, Category.comp_id]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- The native decoder returns the Bit held by the state. -/
theorem unpack_run (x : value Bit) :
    (denoteSingletonRegion J M unpack_typed.hasType).of (Sum.inl x : value State) =
      (pure x : Trace (value Bit)) := by
  obtain ⟨h, d⟩ := RegionDenotes.unpackExits (Φ := signature.Instr) J M [] [Bit]
  have e := RegionDenotes.eq_denote J M d
  have unit : (λ_ ((M).obj State)).inv ≫
      CartesianMonoidalCategory.snd (ctxObj M []) ((M).obj State) = 𝟙 _ :=
    CartesianMonoidalCategory.leftUnitor_inv_snd _
  have collapse : (λ_ ((M).obj State)).inv ≫
      (CartesianMonoidalCategory.snd (ctxObj M []) ((M).obj State) ≫ unpackLabel M [Bit]) ≫
        singletonLabelPayload M Bit = unpackLabel M [Bit] ≫ singletonLabelPayload M Bit := by
    rw [Category.assoc, reassoc_of% unit]
  have morph : packedLabelInject M 0 (rfl : At [Bit] 0 Bit) ≫
      (unpackLabel M [Bit] ≫ singletonLabelPayload M Bit) = 𝟙 _ := by
    rw [← labelInject_packLabel, Category.assoc, reassoc_of% (packLabel_unpackLabel M [Bit])]
    exact SingletonDispatcher.labelInject_payload M Bit
  have value := ConcreteCategory.congr_hom morph x
  unfold denoteSingletonRegion
  rw [← e, ← (J).map_comp, ← (J).map_comp, collapse, ← packedInject_apply]
  exact congrArg (pure (f := Trace)) value

set_option backward.isDefEq.respectTransparency false in
theorem step_run_in (p : Program) (s : value State) : ((F).map (stepArrow p)).of s = stepIn p s := by
  let U : (J).obj ((M).obj State) ⟶ (J).obj ((M).obj Bit) :=
    denoteSingletonRegion J M unpack_typed.hasType
  let P : (J).obj ((M).obj Bit) ⟶ (J).obj ((M).obj (packedExitType Exits)) :=
    denoteSingletonRegion J M p.typed.packExits.hasType
  have hu : (F).map (ofRegion N unpack_typed) = U :=
    Paper.Extension.Singleton.denoteFunctor_map_ofRegion J M (fun _ _ => ⟨rfl, rfl⟩)
      (WithGuardedTablePacking.seedDenotes false J M (fun _ _ => ⟨rfl, rfl⟩)) unpack_typed
  have hp : (F).map (ofRegion N p.typed.packExits) = P :=
    Paper.Extension.Singleton.denoteFunctor_map_ofRegion J M (fun _ _ => ⟨rfl, rfl⟩)
      (WithGuardedTablePacking.seedDenotes false J M (fun _ _ => ⟨rfl, rfl⟩)) p.typed.packExits
  have comp : (F).map (stepArrow p) = U ≫ P := by
    rw [stepArrow_eq, Functor.map_comp, hu, hp]
  have run : ((F).map (stepArrow p)).of s = (U ≫ P).of s :=
    congrArg (fun g : (J).obj ((M).obj State) ⟶ (J).obj ((M).obj (packedExitType Exits)) => g.of s) comp
  rw [run]
  have bind := congrFun (Kleisli.Type.comp_of_eq_kleisliRight Trace U P) s
  refine bind.trans ?_
  rcases s with x | e
  · change Bind.bind (m := Trace) (U.of (Sum.inl x)) (fun y => P.of y) = P.of x
    rw [show U.of (Sum.inl x) = (pure x : Trace (value Bit)) from unpack_run x, pure_bind]
  · exact e.elim

set_option backward.isDefEq.respectTransparency false in
/-- The literal loop runs the model's iterator on the step. -/
theorem loop_run_in (p : Program) (s : value State) :
    (denoteSingletonRegion J M (loop_typed p).hasType).of s =
      Silmaril.Elgot.iter (m := Trace) (stepIn p) s := by
  have literal : (F).map (loopArrow p) = denoteSingletonRegion J M (loop_typed p).hasType :=
    Paper.Extension.Singleton.denoteFunctor_map_ofRegion J M (fun _ _ => ⟨rfl, rfl⟩)
      (WithGuardedTablePacking.seedDenotes false J M (fun _ _ => ⟨rfl, rfl⟩)) (loop_typed p)
  have steps : (fun x : value State =>
      (((F).map (stepArrow p)).of x : Trace (value Bit ⊕ value State))) = stepIn p :=
    funext (step_run_in p)
  have iterated : (F).map (iterateSum N (stepArrow p)) =
      denoteSingletonRegion J M (loop_typed p).hasType :=
    (congrArg (F).map (loopArrow_eq p)).symm.trans literal
  exact ((congrArg (fun g : (J).obj ((M).obj State) ⟶ (J).obj ((M).obj Bit) => g.of s) iterated).symm.trans
    (map_iterateSum_of (stepArrow p) s)).trans
      (congrArg (fun f => Silmaril.Elgot.iter (m := Trace) f s) steps)

end Coherent

/-! ## The four-reply model -/

noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

theorem step_run (p : Program) (s : value State) : ((F).map (stepArrow p)).of s = stepModel p s :=
  step_run_in p s

theorem loop_run (p : Program) (s : value State) :
    (denoteSingletonRegion J M (loop_typed p).hasType).of s =
      Silmaril.Elgot.iter (m := Trace) (stepModel p) s :=
  loop_run_in p s

/-- On a Bit state the step has the outcomes of the reflected request tree. -/
theorem stepModel_outcomes (p : Program) (g : Bool) :
    (stepModel p (Sum.inl (bit g))).outcomes = p.tree.outcomes (fun _ => g) :=
  p.observations_eq g

theorem loopObservations_eq (p : Program) (g : Bool) :
    loopObservations p g = (Silmaril.Elgot.iter (m := Trace) (stepModel p) (Sum.inl (bit g))).outcomes :=
  congrArg Tagged.outcomes (loop_run p (Sum.inl (bit g)))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop
