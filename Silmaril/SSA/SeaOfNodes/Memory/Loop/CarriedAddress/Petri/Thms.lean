module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri.Correctness

/-! Complete observations of the emitted coloured loop with an address Phi. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri

open RVSDG (Tuple)
open RVSDG.NestedTheta.Petri (Finishes)
open SeaOfNodes.Loop (Incoming)
open Silmaril.MLIR.MemRef (Buffer)

variable {args : List ValueSort} {cells : Nat}

/-- The actual θ body selects the incoming address. Its completion
publishes the tail tag, the next occurrence, and the whole post-store heap
with all invariant inputs. -/
theorem lowerBody_run (graph : Graph args) (input : Tuple (Val cells) args) (arrival : Incoming)
    (heap : Heap cells) (fuel : Nat) :
    (lowerBody graph).run (thetaRuntime cells) fuel (encodeArrival arrival heap input) =
      some (match graph.step input arrival heap with
        | .inl (_, final) => .cons ⟨0⟩ (encodeArrival .entry final input)
        | .inr next => .cons ⟨1⟩ (encodeArrival .backedge next input)) :=
  Proofs.lowerBody_run graph input arrival heap fuel

/-- With `budget + 1` θ activations, the numbered graph agrees with the
native loop at backedge allowance `budget`. -/
theorem lower_run (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) (budget : Nat) :
    (lower graph).run (thetaRuntime cells) (budget + 1) (encodeArrival .entry heap input) =
      (graph.evalWithin input budget .entry heap).map (fun (word, final) => encodeResult word final) :=
  Proofs.lower_run graph input heap budget

/-- A finite firing sequence from a single entry marking preserves and
reflects the native loop's complete return. -/
theorem lower_finishes_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) (word : Word) (final : Heap cells) :
    Finishes (thetaRuntime cells) (lower graph) (encodeArrival .entry heap input) (encodeResult word final) ↔
      ∃ budget, graph.evalWithin input budget .entry heap = some (word, final) :=
  Proofs.lower_finishes_iff graph input heap word final

/-- A completed coloured firing trace and a successful emitted MemRef CFG
run witness the same word and every final cell at independent bounds. -/
theorem finishes_iff_memref_run (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) (word : Word) (final : Heap cells) :
    Finishes (thetaRuntime cells) (lower graph) (encodeArrival .entry heap input) (encodeResult word final) ↔
      ∃ budget, MemRef.run graph input budget ⟨heap⟩ = some (word, Buffer.mk final) :=
  Proofs.finishes_iff_memref_run graph input heap word final

/-- Absence of a finite completion agrees with absence at every MemRef
backedge allowance. -/
theorem no_finishes_iff_memref_none (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) :
    (∀ word final, ¬ Finishes (thetaRuntime cells) (lower graph) (encodeArrival .entry heap input)
      (encodeResult word final)) ↔
      ∀ budget, MemRef.run graph input budget ⟨heap⟩ = none :=
  Proofs.no_finishes_iff_memref_none graph input heap

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri
