module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingUnaryProducer

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer (lowering_post_denotation)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Example (singleBind_typed singleBindArrow)
open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open Paper.WithComputedCallReturns.Example (Payload)
open Paper.WithComputedCallReturns.Example.ITree (TreeModel raw compatible)
open Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample (Result keepInput_typed)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example
  (Seed explicitArrow treeInterpretation)
open Paper.Extension.Singleton (ofRegion)

open Paper.WithComputedCallReturns.Example (Atom operand_typed)
open Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample (explicitSequence_typed)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls (denoteFunctor)
open Paper.Extension.Singleton (denoteFunctor_map_ofRegion)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Semantics.Interaction.Typed
open scoped MonoidalCategory

attribute [local instance] typeModel categoricalInstructions

theorem retained_images_eq : treeInterpretation.map explicitArrow = treeInterpretation.map singleBindArrow := by
  let := regionTypingCoherent raw compatible
  let J := typeJ (m := TreeModel)
  let M := Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)
  change (denoteFunctor false J M (fun _ _ => ⟨rfl, rfl⟩)).map (ofRegion Seed explicitSequence_typed) =
    (denoteFunctor false J M (fun _ _ => ⟨rfl, rfl⟩)).map (ofRegion Seed singleBind_typed)
  unfold denoteFunctor
  rw [denoteFunctor_map_ofRegion, denoteFunctor_map_ofRegion]
  exact congrArg (fun f => J.map ((λ_ (M.obj Payload)).inv) ≫
    f ≫ J.map (Semantics.Categorical.singletonLabelPayload M Result))
    (lowering_post_denotation J M (fun _ _ => ⟨rfl, rfl⟩) operand_typed (.op (.var rfl)) keepInput_typed)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingUnaryProducer
