module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Example.Defs

/-! # Run the numbered graph on the nested CF fixture and all three inputs -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Example

open SeaOfNodes.Loop.MLIR.CF (model)
open SeaOfNodes.MLIR (Word)
open Nested.MLIR.CF.Example (checked mask projected source)
open Diamond.MLIR.CF.Example (constant input result selector width)
open Blocks (Bank)

def keptResult : KeptResult checked (mask := mask) :=
  (checkResult checked mask).get (by rfl)

def runRVSDG (activations : Nat) : Option Nat :=
  ((lower checked projected keptResult).run (Join.model model) activations input).map
    (fun values => (values.get .head).toNat)

/-- Vary only the selector before the first header and execute the actual
numbered merge region. These three inputs exercise both γ nodes. -/
def probe (value : Word width) : Nat × Option Nat :=
  let old := (constant selector value).eval model ((source 0).body.eval model input)
  let occurrence := checked.selected model old
  let bank := (mergeRegion checked projected).toGraph.run (Join.model model) 0 (mask.project old)
  ((checked.predecessor occurrence).val, bank.map (fun merged => (merged.get result).toNat))

def incoming : List (Nat × Option Nat) :=
  [probe 3, probe 2, probe 1]

/-- Read the carried arity from the actual numbered θ vertex. -/
def thetaArity : Nat :=
  let carried := SeaOfNodes.Diamond.dataPorts mask.kept
  let past := (source 0).body.producers
  match lower checked projected keptResult with
  | .region nodes _ _ => (nodes (SeaOfNodes.Diamond.lastIndex carried past)).ins.length

def sourceBudget (activations : Nat) : Nat :=
  sourceVisits checked model activations input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Example
