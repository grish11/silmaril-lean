module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Correctness

/-! # Finite observations of the two-address θ and its coloured net -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri

open RVSDG (Tuple)
open RVSDG.NestedTheta.Petri (Finishes)

variable {args : List ValueSort} {cells : Nat}

/-- The emitted entry wires seed both address lanes and the entire initial heap. -/
theorem read_entryWires (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) :
    (entryWires graph).read (encodeInput heap input) PUnit.unit =
      encodeHeader (graph.seed input heap) input :=
  Proofs.read_entryWires graph input heap

/-- The numbered child emits the native tail tag, both simultaneous
feedback operands and the entire post-store heap. -/
theorem lowerActivation_run (graph : Graph args) (input : Tuple (Val cells) args) (header : Header cells)
    (fuel : Nat) :
    (lowerActivation graph).run (thetaRuntime cells) fuel (encodeHeader header input) =
      some (activationPacket graph input header) :=
  Proofs.lowerActivation_run graph input header fuel

/-- The exact packet is also the finite completion observation of the
coloured child region. -/
theorem lowerActivation_finishes_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (header : Header cells) (packet : Tuple (WireVal cells) (Packet args)) :
    Finishes (thetaRuntime cells) (lowerActivation graph) (encodeHeader header input) packet ↔
      packet = activationPacket graph input header :=
  Proofs.lowerActivation_finishes_iff graph input header packet

/-- Numbered θ fuel counts the initial activation as well as allowed
backedges. The returned tuple contains the word and every cell. -/
theorem lower_run (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells)
    (budget : Nat) :
    (lower graph).run (thetaRuntime cells) (budget + 1) (encodeInput heap input) =
      (graph.evalWithin input budget (graph.seed input heap)).map
        (fun (word, final) => encodeResult word final) :=
  Proofs.lower_run graph input heap budget

/-- Starting from one entry marking, finite coloured completion preserves
and reflects the exact native result. Firing and native backedge witnesses
have independent lengths. -/
theorem lower_finishes_iff (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells)
    (word : Word) (final : Heap cells) :
    Finishes (thetaRuntime cells) (lower graph) (encodeInput heap input) (encodeResult word final) ↔
      graph.Returns input heap word final :=
  Proofs.lower_finishes_iff graph input heap word final

/-- Absence of any finite coloured completion agrees with absence of a
native return at every backedge allowance. -/
theorem no_finishes_iff (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) :
    (∀ output, ¬ Finishes (thetaRuntime cells) (lower graph) (encodeInput heap input) output) ↔
      ∀ budget, graph.evalWithin input budget (graph.seed input heap) = none :=
  Proofs.no_finishes_iff graph input heap

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri
