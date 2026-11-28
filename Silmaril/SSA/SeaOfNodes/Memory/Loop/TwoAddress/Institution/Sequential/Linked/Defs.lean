module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Wrapper.Thms

/-! One checked numbered graph containing both original θ bodies. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked

open RVSDG (Tuple)
open RVSDG.NestedTheta.ExplicitRuntime (EntryChecked)
open RVSDG.NestedTheta.ExplicitRuntime.Splice (graphChecked)

variable {ambient next : List ValueSort}

def lower (first : Graph ambient) (second : Graph next) (wiring : Boundary.Wiring ambient next) :
    RVSDG.NestedTheta.Graph ThetaOpcode (carrier ambient) []
      [carrier (activationArgs ambient), carrier (activationArgs next)] (carrier [.word, .word]) :=
  RVSDG.NestedTheta.ExplicitRuntime.Splice.graph (Wrapper.producerChecked first)
    (graphChecked (Boundary.checked wiring) (Wrapper.consumerChecked second))

def checked (first : Graph ambient) (second : Graph next) (wiring : Boundary.Wiring ambient next) :
    EntryChecked (a := inputData ambient) (b := inputData [.word, .word]) (lower first second wiring).toTerm :=
  graphChecked (Wrapper.producerChecked first) (graphChecked (Boundary.checked wiring) (Wrapper.consumerChecked second))

def resultCodec (cells : Nat) : Result cells ≃ Tuple (WireVal cells) (carrier [.word, .word]) where
  toFun out := Wrapper.pairPacket out.1 out.2.1 out.2.2
  invFun
    | .cons first (.cons second (.cons heap .nil)) => (first, second, heap)
  left_inv _ := rfl
  right_inv
    | .cons _ (.cons _ (.cons _ .nil)) => rfl

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked
