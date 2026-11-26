module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Example.Defs

/-! Recheck the real guarded loop with an unused i16 capture. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded.Example

open SeaOfNodes.Diamond (Val ValueSort)
open SeaOfNodes.Loop.MLIR.CF (model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open SCCP.Dispatch (Checked)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (entry width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted)
open Reindex.Guarded.Institution (Generated Valuation)
open Reindex.Guarded.Institution.Example (initialSignature original)

abbrev captureWidth : Width := ⟨16, by decide⟩
abbrev capture : ValueSort Width := .data captureWidth
abbrev widened := extend initialSignature capture

def input (value : Word captureWidth) (side : Bool) : Valuation widened :=
  RVSDG.Tuple.cons (F := Val Word) (t := .value capture) value (entry true side)

def checked : Option (Generated widened width) :=
  (compile capture original).toOption

def checkedSide : Option Bool :=
  checked.map fun artifact =>
    @Checked.side _ _ _ _ model _ widened.bankEq _ (@Admitted.checked _ _ widened.bankEq artifact.source)

/-- Run the actual fresh artifacts from FIFO replay on the enlarged bank. -/
def run (value : Word captureWidth) (side : Bool) : Option (Option Nat × Option Nat × Option Nat) := do
  let generated ← checked
  let bank := input value side
  let source := @Admitted.source _ _ widened.bankEq generated.source
  let cfFuel := if side then 6 else 7
  return ((source.source.runFrom model 5 0 bank).map BitVec.toNat,
    (generated.artifacts.cf.run evalOp cfFuel (encodeValues bank)).map (fun env => (env.get .here).toNat),
    (generated.artifacts.numbered.2.run (Join.model model) 1 bank).map (fun packet => (packet.get .head).toNat))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded.Example
