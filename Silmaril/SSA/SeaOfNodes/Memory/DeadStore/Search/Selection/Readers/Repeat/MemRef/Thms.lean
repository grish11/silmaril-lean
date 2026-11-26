module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.MemRef.Defs
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms
import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.MemRef

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe lower_run lower_returns_iff)

variable {cells : Nat} {args : List ValueSort}

/-- At the checked scalar input, both emitted blocks return the same word
and entire final buffer for every initialized buffer. -/
theorem runOptimized_eq_runOriginal (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Buffer cells) :
    (lower graph input).runOptimized initial = (lower graph input).runOriginal initial := by
  change observe (Repeat.rewrite graph input).graph input initial = observe graph input initial
  rw [lower_run, lower_run, Repeat.rewrite_denote]

/-- The optimized block preserves and reflects the original graph's finite
return, with the heap represented by the buffer's cell function. -/
theorem runOptimized_returns_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    (lower graph input).runOptimized ⟨initial⟩ = (word, Buffer.mk final) ↔
      graph.Returns input initial word final := by
  rw [runOptimized_eq_runOriginal]
  exact (lower_returns_iff graph input initial word final).symm

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.MemRef
