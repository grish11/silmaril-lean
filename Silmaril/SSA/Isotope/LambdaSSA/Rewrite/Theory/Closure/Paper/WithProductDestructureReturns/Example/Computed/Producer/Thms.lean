module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Example.Computed.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.BinaryLet.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ComputedProductProducer

/-! # The effectful product producer boundary in the product-destructure join -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.Example.Computed

open Silmaril.Isotope.LambdaSSA
open Paper.WithComputedCallReturns.Example (Payload)
open Paper.RetainedLet.Generation.Example (Op)
open Paper.RetainedLet (returnOnce returnOnce_typed)
open Paper.SingletonReification.BinaryLet (returnPair returnPair_typed)
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff)

/-- The joined contextual quotient distinguishes native destructuring from the
once-only return when the product's right field performs a primitive call. -/
theorem computed_product_producer_fails :
    ¬ Paper.Extension.Eqv Seed [Payload]
      (returnPair (.pair (.var 0) (.op Op.produce (.var 0))))
      (returnOnce (.pair (.var 0) (.op Op.produce (.var 0)))) [Packet] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.computed_product_producer_fails

/-- The same separation at the exact guarded singleton hom interface. -/
theorem computed_product_producer_ne :
    ofRegion Seed (returnPair_typed packet_typed) ≠ ofRegion Seed (returnOnce_typed packet_typed) :=
  fun h => computed_product_producer_fails ((ofRegion_eq_iff Seed _ _).1 h)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.Example.Computed
