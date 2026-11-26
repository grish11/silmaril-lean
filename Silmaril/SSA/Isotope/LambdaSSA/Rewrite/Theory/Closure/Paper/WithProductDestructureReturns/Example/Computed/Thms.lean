module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Generation.Example.Defs

/-! # Returning a destructure after a computed product -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.Example.Computed

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.WithComputedCallReturns.Example (Atom Payload)
open Paper.RetainedLet.Generation.Example (Op producer_typed packedBody_typed)
open Paper.RetainedLet (unpackTerm_typed)
open Paper.PackedBody (applyPackedTerm_typed)
open Paper.Extension.Singleton (ofRegion)
open Paper.Extension.Singleton.Generation (Generated)
open CfgEta.TypeCategory (returnRegion_typed)

abbrev Packet := product Payload Payload

/-- Produce a pair of the original input and the primitive's result. -/
theorem packet_typed : Tm.HasType [Payload] (.pair (.var 0) (.op Op.produce (.var 0))) Packet :=
  .pair (.var (i := 0) rfl) producer_typed

theorem consumerReturn_typed :
    Tm.HasType [Packet] (.let₁ (.op Op.consume (.var 0)) (.var 0)) Payload :=
  .let₁ packedBody_typed (.var (i := 0) rfl)

/-- Open both fields, call the consumer with their pair, and return its reply. -/
theorem consumer_typed :
    Tm.HasType [Packet]
      (.let₂ (.var 0) (.let₁ (.op Op.consume (.pair (.var 1) (.var 0))) (.var 0))) Payload :=
  unpackTerm_typed (applyPackedTerm_typed consumerReturn_typed)

abbrev Seed := JoinedStep (τ := Ty Atom) (Φ := Op) false

/-- The new destructuring case composes with an effectful product producer. -/
theorem sequence_generated :
    Generated Seed (ofRegion Seed (returnRegion_typed
      (.let₁ packet_typed (consumer_typed.rename ((Ren.wk [] Payload).lift Packet))))) :=
  let input : Tm.BranchValue [Packet] (.var 0 : Tm Op) Packet := .var rfl
  let result : Tm.BranchValue [Payload] (.var 0 : Tm Op) Payload := .var rfl
  generated_returnFragment false (.seq (ha := packet_typed) (hb := consumer_typed)
    (.pair (.value result) (.primitive Op.produce result))
    (.destructure (hc := consumerReturn_typed) rfl (.seq (.primitive Op.consume input) (.value result))))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.Example.Computed
