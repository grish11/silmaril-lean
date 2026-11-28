module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Correctness

/-! Exact frame and buffer agreement for the occurrence-selected address. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef

open RVSDG (Tuple)
open RVSDG.NestedTheta.Petri (Finishes)
open SeaOfNodes.Loop (Incoming)
open Silmaril.MLIR.CF.Ordered (Block)
open Silmaril.MLIR.MemRef (Buffer)

variable {cells : Nat} {args : List ValueSort}

/-- The entry edge supplies the first occurrence without modifying any cell. -/
theorem entry_transition (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) :
    Block.eval (evalBody graph input) (lower cells graph).entry .nil ⟨heap⟩ =
      (.inl ⟨Label.header, arrivalEnv .entry⟩, ⟨heap⟩) :=
  rfl

/-- At either arrival, the emitted terminator takes the native successor.
A restart supplies the backedge occurrence and the entire post-store
buffer. An exit supplies the word and the entire final buffer. -/
theorem header_transition (graph : Graph args) (input : Tuple (Val cells) args)
    (arrival : Incoming) (heap : Heap cells) :
    Block.eval (evalBody graph input) ((lower cells graph).block .header) (arrivalEnv arrival) ⟨heap⟩ =
      match graph.step input arrival heap with
      | .inl (word, final) => (.inl ⟨Label.exit, .cons word .nil⟩, ⟨final⟩)
      | .inr next => (.inl ⟨Label.header, arrivalEnv .backedge⟩, ⟨next⟩) :=
  Proofs.header_transition graph input arrival heap

/-- At the selected typed input, the existing coloured activation's
completion selects the same successor and supplies the same entire
post-store heap as the emitted CF header. -/
theorem petri_activation_iff_header (graph : Graph args) (input : Tuple (Val cells) args)
    (arrival : Incoming) (heap next : Heap cells) (restart : Bool) :
    Finishes (thetaRuntime cells) graph.activation.activation
        (Memory.encodeInput heap (graph.operands input arrival))
        (.cons ⟨if restart then 1 else 0⟩ (Memory.encodeInput next (graph.operands input arrival))) ↔
      Block.eval (evalBody graph input) ((lower cells graph).block .header)
          (arrivalEnv arrival) ⟨heap⟩ =
        (.inl (if restart then ⟨Label.header, arrivalEnv .backedge⟩
          else ⟨Label.exit, .cons (graph.activation.stopWord (graph.operands input arrival)) .nil⟩),
          ⟨next⟩) :=
  Proofs.petri_activation_iff_header graph input arrival heap next restart

/-- With `budget + 3` CF block steps, the complete return (or its absence
within the given backedge allowance) agrees with native execution. -/
theorem run_eq_evalWithin (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (heap : Heap cells) :
    run graph input budget ⟨heap⟩ =
      (graph.evalWithin input budget .entry heap).map (fun (word, final) => (word, Buffer.mk final)) :=
  Proofs.run_eq_evalWithin graph input budget heap

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef
