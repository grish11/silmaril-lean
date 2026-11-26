module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.BranchBinding.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Example.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.BranchBinding.Singleton.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Example.Computed.Producer.Thms

/-! # A raw product with one effectful field -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding.Example

open Silmaril.Isotope.LambdaSSA
open Paper.WithComputedCallReturns.Example (Atom)
open Paper.WithProductDestructureReturns.Example.Computed (packet_typed)
open Paper.RetainedLet.Generation.Example (Op)
open Paper.SingletonReification.BinaryLet (returnPair_typed applyPackedPair_typed)
open Paper.RetainedLet (returnOnce_typed)
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding

local notation "Old" =>
  WithProductDestructureReturns.BranchBinding.singletonSeed (τ := Ty Atom) (Φ := Op) false
local notation "New" => singletonSeed (τ := Ty Atom) (Φ := Op) false

/-- The old raw product quotient separates destructure-and-rebuild from the
bare branch on the computed pair. -/
theorem old_raw_producer_ne :
    Singleton.rawClass Old (returnPair_typed packet_typed).hasType ≠
      Singleton.rawClass Old (.br (ℓ := 0) rfl packet_typed) := fun h =>
  WithProductDestructureReturns.Example.Computed.computed_product_producer_fails
    ((WithProductDestructureReturns.joined_guarded_eqv_iff
      (returnPair_typed packet_typed) (returnOnce_typed packet_typed)).mp
        ((Quotient.exact h).trans (.extra (.br rfl packet_typed) (returnOnce_typed packet_typed).hasType
          (.inr (.bind rfl packet_typed)))))

/-- The new raw generator applies to the same literal endpoints. -/
theorem raw_producer_eq :
    Singleton.rawClass New (returnPair_typed packet_typed).hasType =
      Singleton.rawClass New (.br (ℓ := 0) rfl packet_typed) :=
  raw_class_producer_eq false packet_typed

/-- The native binary let with that exact single-call scrutinee is generated. -/
theorem raw_native_computed_binary_generated :
    Singleton.Generation.Generated New (Singleton.rawClass New
      (ValueBranches.let₂ packet_typed
        (applyPackedPair_typed WithComputedProductProducers.Example.packedBody)).hasType) :=
  raw_generated_guardedFragment false
    (.let₂Computed (.pair (.value (.var rfl)) (.primitive Op.produce (.var rfl))) (.branch (.var rfl)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding.Example
