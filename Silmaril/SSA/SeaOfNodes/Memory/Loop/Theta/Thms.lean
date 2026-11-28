module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Theta.Activation
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Theta.Correctness

/-! # Finite observations of the numbered memory θ -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop

open RVSDG (Tuple Wires)
open RVSDG.OrderedRuntime.Structured (Ty)

variable {args : List ValueSort} {cells : Nat}

/-- Reading the positional argument wires of a closed memory region
reconstructs the complete typed input tuple. -/
theorem read_argWires {entry : List (Ty ValueSort)} (input : Tuple (WireVal cells) entry) :
    Wires.read (SeaOfNodes.Loop.argWires entry []) input PUnit.unit = input :=
  ThetaProofs.read_args input

/-- Each θ activation runs the memory table, calculates the tag from its
exported word, and puts its last heap on the common stop/continue boundary. -/
theorem Graph.thetaBody_run (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) :
    graph.thetaBody.run (thetaRuntime cells) (encodeInput heap input) =
      let out := graph.body.denote input heap
      .cons (continueTag out.1 (graph.stopWord input)) (encodeInput out.2 input) :=
  ThetaProofs.body_run graph input heap

/-- The numbered target preserves and reflects the whole source output. -/
theorem Graph.lowerTheta_returns_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (value : Word) (final : Heap cells) :
    graph.Returns input initial value final ↔
      graph.lowerTheta.Returns (thetaRuntime cells) (encodeInput initial input) (encodeResult value final) :=
  ThetaProofs.lower_returns graph input initial value final

/-- The first successful numbered run has one activation more than the
number of completed source backedges. -/
theorem Graph.lowerTheta_returnsAfter_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (count : Nat) (value : Word) (final : Heap cells) :
    graph.ReturnsAfter input initial count value final ↔
      graph.lowerTheta.run (thetaRuntime cells) count (encodeInput initial input) = none ∧
      graph.lowerTheta.run (thetaRuntime cells) (count + 1) (encodeInput initial input) =
        some (encodeResult value final) :=
  ThetaProofs.lower_returnsAfter graph input initial count value final

/-- A fixed backedge keeps requesting another completed activation and
excludes a return at every numbered bound. -/
theorem Graph.lowerTheta_run_none_of_fixed_backedge (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) (fixed : graph.step input heap = .inr heap) (fuel : Nat) :
    graph.lowerTheta.run (thetaRuntime cells) fuel (encodeInput heap input) = none :=
  ThetaProofs.lower_run_none graph input heap fixed fuel

end Silmaril.SSA.SeaOfNodes.Memory.Loop
