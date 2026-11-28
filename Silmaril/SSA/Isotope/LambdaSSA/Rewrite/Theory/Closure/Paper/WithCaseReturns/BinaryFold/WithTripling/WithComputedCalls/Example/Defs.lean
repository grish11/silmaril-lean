module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Generation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCall.Example.Defs

/-! # The same two calls and retained input in the new quotient -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open Paper.WithComputedCallReturns.Example (Atom Op Payload)
open Paper.WithComputedCallReturns.Example.ITree (TreeModel raw compatible)
open Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample
  (Result source_typed explicitSequence_typed)
open Paper.Extension.Singleton (ofType ofRegion)
open Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)

abbrev Seed := Step (τ := Ty Atom) (Φ := Op) false

def sourceArrow : ofType Seed Payload ⟶ ofType Seed Result := ofRegion Seed source_typed

def explicitArrow : ofType Seed Payload ⟶ ofType Seed Result := ofRegion Seed explicitSequence_typed

attribute [local instance] typeModel categoricalInstructions

/-- The coherent free ITree interpretation descends through the new seed. -/
noncomputable def treeInterpretation :
    TypeCategory (τ := Ty Atom) (Φ := Op) false ⥤ Kleisli (ofTypeMonad TreeModel) :=
  letI := regionTypingCoherent raw compatible
  denoteFunctor false (typeJ (m := TreeModel))
    (Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)) (fun _ _ => ⟨rfl, rfl⟩)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example
