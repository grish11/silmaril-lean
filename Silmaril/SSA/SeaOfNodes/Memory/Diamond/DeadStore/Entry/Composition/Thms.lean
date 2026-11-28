module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (run)

variable {args : List ValueSort} {cells : Nat}
variable {entry : Memory.Graph args}

/-- Recognizing a singleton entry Store preserves the boundary heap. -/
theorem asPrefixStore_heap {store : PrefixStore args} (recognized : asPrefixStore entry = some store)
    (input : Tuple (Val cells) args) (initial : Heap cells) :
    (store.table.denote input initial).2 = (entry.denote input initial).2 :=
  Proofs.asPrefixStore_heap recognized input initial

theorem rewriteResidual_checked {graph : Graph args} {result : Discovery.Result args}
    (input : Tuple (Val cells) args) (accepted : rewriteResidual graph entry input = some result) :
    ∃ store, asPrefixStore entry = some store ∧ Discovery.rewrite ⟨store, graph⟩ input = some result :=
  Option.bind_eq_some_iff.mp accepted

theorem rewriteResidual_denote {graph : Graph args} {result : Discovery.Result args}
    (input : Tuple (Val cells) args) (accepted : rewriteResidual graph entry input = some result)
    (guard : Bool) (initial : Heap cells) :
    result.graph.denote guard input initial = graph.denote guard input (entry.denote input initial).2 :=
  Proofs.rewriteResidual_denote input accepted guard initial

/-- Refusal of the all-path step keeps the earlier deletions and their emitted pair. -/
theorem lower_refused (graph : Graph args) (entry : Memory.Graph args) (input : Tuple (Val cells) args)
    (refused : rewriteResidual graph (Entry.lowerRepeated graph entry input).entry input = none) :
    let repeated := Entry.lowerRepeated graph entry input
    lower graph entry input = ⟨repeated.deleted, false, repeated.programs⟩ := by
  simp only [lower, refused]

/-- After entry, one arm, and the join, both CFGs return the original word
and entire final buffer at the checked input. -/
theorem lower_runs (graph : Graph args) (entry : Memory.Graph args) (input : Tuple (Val cells) args)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lower graph entry input).programs
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected :=
  Proofs.lower_runs graph entry input guard fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition
