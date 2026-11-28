module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example.Defs

/-! # Bind the existing nested producer once and retain the original input -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Example

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open Paper.WithComputedCallReturns.Example (Op Payload sequenced sequenced_typed)
open Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCallExample (Result keepInput keepInput_typed)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Example
  (Seed)
open Paper.Extension.Singleton (ofType ofRegion)
open Paper.RetainedLet (returnOnce returnOnce_typed)

/-- Keep the nested term rather than lowering its unary lets. The exact
outward continuation returns the original input with the bound result. -/
def singleBind : Region Op := (returnOnce sequenced).lsubst keepInput

theorem singleBind_typed : ValueBranches [Payload] singleBind [Result] :=
  (returnOnce_typed sequenced_typed).lsubst keepInput_typed

def singleBindArrow : ofType Seed Payload ⟶ ofType Seed Result := ofRegion Seed singleBind_typed

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer.Example
