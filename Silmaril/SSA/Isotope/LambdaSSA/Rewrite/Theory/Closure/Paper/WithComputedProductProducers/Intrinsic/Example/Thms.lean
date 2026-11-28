module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Example.Thms

/-! # Exact elaborations for the computed product examples -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.Example

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.WithComputedCallReturns.Example (Payload)
open Paper.WithProductDestructureReturns.Example.Computed (Packet packet_typed)
open Paper.RetainedLet.Generation.Example (Op)
open Paper.WithComputedProductProducers.Example (Seed packedBody)
open Paper.SingletonReification.BinaryLet (applyPackedPair_typed)
open Paper.Extension.Singleton (ofRegion)
open Paper.Extension.Singleton.Generation (Generated)

def packet : Term Op Payload Packet :=
  .pair .input (.call .produce .input)

/-- Bind the computed fields and return them along with the original input. -/
def native : Program Op Payload (product Payload Packet) :=
  .let₂ Payload Payload packet .branchInput

/-- This is the actual native binary-let witness from the producer extension. -/
theorem native_arrow :
    native.arrow false = ofRegion Seed (.let₂ packet_typed (applyPackedPair_typed packedBody)) :=
  rfl

theorem native_generator : native.arrow false = native.generatorArrow Seed :=
  native.arrow_eq_generatorArrow false

/-- Evaluate the effectful product before destructuring and passing it to the second primitive. -/
def returnedDestructure : Program Op Payload Payload :=
  .returned (.seq packet (.destructure Payload Payload (.call .consume .input)))

theorem returnedDestructure_generated : Generated Seed (returnedDestructure.arrow false) :=
  returnedDestructure.generated false

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.Example
