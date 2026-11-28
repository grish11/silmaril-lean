module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Feedback.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Correctness
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Observation

/-! The emitted CF edges and complete finite observations of the memory loop. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF

open RVSDG (Tuple)
open Silmaril.MLIR.CF.Ordered (Block)
open Silmaril.MLIR.MemRef (Buffer)

variable {cells : Nat} {args : List ValueSort}

/-- The real conditional terminator yields either the exit frame carrying
the word or the backedge frame. Both carry the post-store buffer in the monad. -/
theorem header_transition (graph : Graph args) (input : Tuple (Val cells) args) (initial : Buffer cells) :
    Block.eval (evalBody input) ((lower cells graph).block Label.header) .nil initial =
      match observeActivation graph input initial with
      | .inl (word, final) => (.inl ⟨Label.exit, .cons word .nil⟩, final)
      | .inr next => (.inl ⟨Label.header, .nil⟩, next) :=
  Proofs.header_transition graph input initial

/-- The emitted CFG returns a word and entire buffer with at most the
given number of backedges precisely when the activation driver produces
them at a count within that allowance. -/
theorem run_eq_some_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (initial : Buffer cells) (result : Word × Buffer cells) :
    run graph input budget initial = some result ↔
      ∃ count ≤ budget, runAfter graph input count initial = some result :=
  Proofs.run_eq_some_iff graph input budget initial result

/-- The CFG observation at a backedge allowance agrees with a native
counted return at some count within that allowance. The buffer's cell
function is the native heap at entry and exit. -/
theorem run_eq_some_iff_returnsAfter (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (initial : Heap cells) (word : Word) (final : Heap cells) :
    run graph input budget ⟨initial⟩ = some (word, Buffer.mk final) ↔
      ∃ count ≤ budget, graph.ReturnsAfter input initial count word final :=
  Proofs.run_eq_some_iff_returnsAfter graph input budget initial word final

/-- Raw CFG fuel needs one step for entry, one per header activation, and
one for exit. Each permitted return observes the word and entire final
buffer. -/
theorem cfg_run_eq_some_iff_returnsAfter (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (initial : Heap cells) (word : Word) (final : Heap cells) :
    (lower cells graph).run (evalBody input) fuel .nil ⟨initial⟩ =
        (some (.cons word .nil), Buffer.mk final) ↔
      ∃ count, count + 3 ≤ fuel ∧ graph.ReturnsAfter input initial count word final :=
  Proofs.cfg_run_eq_some_iff_returnsAfter graph input fuel initial word final

/-- The bounded CFG observation is absent exactly when all native exact
counts within its allowance have no return. -/
theorem run_eq_none_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (initial : Heap cells) :
    run graph input budget ⟨initial⟩ = none ↔
      ∀ count ≤ budget, graph.evalAfter input initial count = none :=
  Proofs.run_eq_none_iff graph input budget initial

/-- The union of bounded CFG returns preserves and reflects native
word-and-heap membership in the partial denotation. -/
theorem exists_run_eq_some_iff_mem_denote (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    (∃ budget, run graph input budget ⟨initial⟩ = some (word, Buffer.mk final)) ↔
      (word, final) ∈ graph.denote input initial :=
  Proofs.exists_run_eq_some_iff_mem_denote graph input initial word final

/-- Absence of a finite observation agrees with the native partial denotation. -/
theorem forall_run_eq_none_iff_denote_eq_none (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) :
    (∀ budget, run graph input budget ⟨initial⟩ = none) ↔ graph.denote input initial = Part.none :=
  Proofs.forall_run_eq_none_iff_denote_eq_none graph input initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF
