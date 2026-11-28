module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Example.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded.Example.Defs

/-! Compute a compact bank for a map with repeated i8 operands and an interior i16 gap. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Example

open SeaOfNodes.Diamond (dataPorts)
open SeaOfNodes.Loop.MLIR.CF (model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open RVSDG (Port)
open Identification (PortMap ports)
open Identification.Example (old original)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (word width)
open Reindex.Guarded.Institution (Generated Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature
open Weakening.Guarded.Example (capture captureWidth)

abbrev finalSignature : EntrySignature := { regs := [.predicate, capture, .predicate, word, word] }

def captureMap : PortMap old finalSignature := fun _ => fun
  | .head => .head
  | .tail .head => .tail (.tail .head)
  | .tail (.tail .head) => .tail (.tail (.tail .head))
  | .tail (.tail (.tail .head)) => .tail (.tail (.tail .head))
  | .tail (.tail (.tail (.tail .head))) => .tail (.tail (.tail (.tail .head)))

def keptSlots : List Nat :=
  (ports (dataPorts (compressed captureMap).regs)).map fun p => slot ((embedding captureMap).portMap p.1 p.2)

def oldInput (right : Word width) (route : Bool) : Valuation old :=
  .cons ⟨true⟩ (.cons ⟨route⟩ (.cons (7 : Word width) (.cons right (.cons (0 : Word width) .nil))))

def fill (wide : Word captureWidth) : Valuation finalSignature :=
  .cons ⟨false⟩ (.cons wide (.cons ⟨false⟩ (.cons (0 : Word width) (.cons (0 : Word width) .nil))))

def gap : Port (dataPorts finalSignature.regs) (.value capture) := .tail .head

def liftedGap (right : Word width) (wide : Word captureWidth) : Option Nat :=
  (liftChecked captureMap (oldInput right true) (fill wide)).map fun values => (values.get gap).toNat

def compared : Option (Compared captureMap width) := do
  let source ← original.toOption
  (Factorization.compare captureMap source).toOption

/-- Run the actual staged and direct CF and numbered artifacts at the checked lift. -/
def run (wide : Word captureWidth) (route : Bool) :
    Option ((Option Nat × Option Nat) × (Option Nat × Option Nat)) := do
  let pair ← compared
  let input ← liftChecked captureMap (oldInput 7 route) (fill wide)
  let runTarget (target : Generated finalSignature width) :=
    ((target.artifacts.cf.run evalOp (if route then 6 else 7) (encodeValues input)).map
      (fun env => (env.get .here).toNat),
     (target.artifacts.numbered.2.run (Join.model model) 1 input).map
      (fun packet => (packet.get .head).toNat))
  return (runTarget pair.staged, runTarget pair.direct)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Example
