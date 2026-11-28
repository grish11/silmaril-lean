module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Defs

/-! Rename every register in the fixed two-feedback source profile. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex

open SeaOfNodes.Diamond (ValueSort dataPorts)
open Tail.Diamond.MLIR.CF.Pruned.Reindex (Permutation)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {old new : List (ValueSort Data)} {out : ValueSort Data}

/-- The external and carried banks use the same typed register permutation. -/
abbrev Registers (old new : List (ValueSort Data)) :=
  Permutation (dataPorts old) (dataPorts new)

/-- Push a tuple into the new register order. A target valuation reduces
in the opposite direction using the existing `pull`. -/
def push (order : Registers old new) {F : SeaOfNodes.Diamond.Ty Data → Type w}
    (bank : Tuple F (dataPorts old)) : Tuple F (dataPorts new) :=
  Tail.Diamond.MLIR.CF.Pruned.Reindex.pull order.symm bank

def quad (order : Registers old new) (q : Quad Op old) : Quad Op new :=
  ⟨q.ins, q.result, order _ q.dest, q.op, q.operands.map (fun t => order t)⟩

/-- Keep both feedback occurrence identities and the ordered writes in every
block. The header condition, dispatch selector and return port are renamed too. -/
def program (order : Registers old new) (p : Program Op old out) : Program Op new out where
  preheader := p.preheader.map (quad order)
  header := p.header.map (quad order)
  again := order _ p.again
  select := order _ p.select
  result := order _ p.result
  feedback side := (p.feedback side).map (quad order)

open SeaOfNodes.Diamond.SCCP (tupleFacts)
open SeaOfNodes.Loop.SCCP (bankTuple)

/-- Reorder the carried facts only. Occurrence marks and the returned fact
have no register coordinates. -/
def assignment (order : Registers old new) {value : Data → Type w}
    (state : SCCP.State value old out) : SCCP.State value new out :=
  (state.1, tupleFacts (push order (bankTuple state.2.1)), state.2.2)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex
