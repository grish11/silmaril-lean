module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.WithTripling.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithComputedCalls.Example

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls
  (fromWithTripling computedCall ReturnFragment generated_returnFragment generated_literalLet
    fromWithTripling_comp_denoteFunctor)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example (Seed sourceArrow explicitArrow treeInterpretation)
open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open Paper.WithComputedCallReturns.Example (Atom Op Payload operand_typed nested nested_typed sequenced_typed)
open Paper.WithComputedCallReturns.Example.ITree (TreeModel raw compatible PayloadValue)
open Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample
  (Result keepInput_typed source_typed explicitSequence_typed expected)
open Paper.Extension.Singleton (ofType ofRegion ofRegion_eq_iff)
open Paper.Extension.Singleton.Generation (Generated)
open CfgEta.TypeCategory (returnRegion_typed)
open Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)

open Paper.WithCaseReturns.BinaryFold.WithTripling
open Paper.RetainedLet (unpackBody_typed)

theorem retained_eq : sourceArrow = explicitArrow :=
  (ofRegion_eq_iff Seed source_typed explicitSequence_typed).2
    (.lsubstPost (computedCall false Op.consume operand_typed)
      (returnRegion_typed nested_typed) (returnRegion_typed sequenced_typed)
      (fun _ _ hi => (keepInput_typed hi).hasType))

theorem projection_identifies_distinct :
    ComputedCallExample.sourceArrow ≠ ComputedCallExample.explicitArrow ∧
      (fromWithTripling false).map ComputedCallExample.sourceArrow =
        (fromWithTripling false).map ComputedCallExample.explicitArrow :=
  ⟨ComputedCallExample.retained_ne, retained_eq⟩

private theorem nested_fragment : ReturnFragment false nested_typed := by
  let hv : Tm.BranchValue [Payload] (.var 0 : Tm Op) Payload := .var rfl
  let ha := Tm.HasType.op (f := Op.produce) hv.hasType
  have operand : ReturnFragment false operand_typed :=
    .seq (ha := ha) (hb := hv.hasType) (.call Op.produce (.value hv)) (.value hv)
  exact .call Op.consume operand

theorem further_call_generated :
    Generated Seed (ofRegion Seed (returnRegion_typed (.op (f := Op.produce) nested_typed))) :=
  generated_returnFragment false (.call Op.produce nested_fragment)

theorem source_generated : Generated Seed sourceArrow := by
  let body : ValueBranches [Payload, Payload] (.br 0 (.pair (.var 1) (.var 0)) : Region Op) [Result] :=
    .br (ℓ := 0) rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))
  let identity : ValueBranches [Result] (.br 0 (.var 0) : Region Op) [Result] := .br (ℓ := 0) rfl (.var (i := 0) rfl)
  have eq := (ofRegion_eq_iff Seed (unpackBody_typed body) identity).2
    (.paper (.productEta (.let₂Eta rfl rfl)))
  have gen : Generated Seed (ofRegion Seed identity) :=
    Paper.Extension.Singleton.Generation.generated_branchValue Seed (.var (i := 0) rfl)
  exact generated_literalLet false nested_typed body rfl
    (generated_returnFragment false nested_fragment) (eq.symm ▸ gen)

attribute [local instance] typeModel categoricalInstructions

theorem source_visible (x : PayloadValue) : (treeInterpretation.map sourceArrow).of x = expected x := by
  let := regionTypingCoherent raw compatible
  have factor : fromWithTripling false ⋙ treeInterpretation = ComputedCallExample.treeInterpretation :=
    fromWithTripling_comp_denoteFunctor false (typeJ (m := TreeModel))
      (Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)) (fun _ _ => ⟨rfl, rfl⟩)
  have maps : treeInterpretation.map sourceArrow =
      ComputedCallExample.treeInterpretation.map ComputedCallExample.sourceArrow := by
    have h := Functor.congr_hom factor ComputedCallExample.sourceArrow
    change treeInterpretation.map sourceArrow =
      𝟙 _ ≫ ComputedCallExample.treeInterpretation.map ComputedCallExample.sourceArrow ≫ 𝟙 _ at h
    simpa only [Category.comp_id, Category.id_comp] using h
  rw [maps]
  exact ComputedCallExample.source_visible x

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithComputedCalls.Example
