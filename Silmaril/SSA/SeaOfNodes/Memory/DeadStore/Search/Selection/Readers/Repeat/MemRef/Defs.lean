module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs

/-! Lower both sides of a checked straight-line deletion pass to typed MemRef blocks. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.MemRef

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Block Buffer wordPorts)
open SeaOfNodes.Memory.MLIR.MemRef (entryPorts encodeInput)
open SeaOfNodes.Memory.MLIR.MemRef renaming lower → lowerMemory

abbrev Program (cells : Nat) (args : List ValueSort) :=
  Block cells [entryPorts cells args] (wordPorts cells)

structure Lowered (cells : Nat) (args : List ValueSort) where
  input : Tuple (Val cells) args
  original : Program cells args
  optimized : Program cells args
  deleted : Nat

variable {cells : Nat} {args : List ValueSort}

/-- Lower the actual source and rewritten graphs, and retain the
scalar input at which the reader certificates were validated. -/
def lower (graph : Graph args) (input : Tuple (Val cells) args) : Lowered cells args :=
  let result := Repeat.rewrite graph input
  ⟨input, lowerMemory cells graph, lowerMemory cells result.graph, result.deleted⟩

def run (program : Program cells args) (input : Tuple (Val cells) args) (initial : Buffer cells) :
    Word × Buffer cells :=
  let (result, final) := Silmaril.MLIR.MemRef.run program (encodeInput input, PUnit.unit) initial
  (result.get .head, final)

def Lowered.runOriginal (programs : Lowered cells args) : Buffer cells → Word × Buffer cells :=
  run programs.original programs.input

def Lowered.runOptimized (programs : Lowered cells args) : Buffer cells → Word × Buffer cells :=
  run programs.optimized programs.input

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.MemRef
