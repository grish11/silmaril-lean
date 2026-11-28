module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Example.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded.Example.Defs

/-! Contract two read-only i8 operands, then insert an unused i16 between two predicates. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Example

open SeaOfNodes.Loop.MLIR.CF (model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Identification (Refusal)
open Identification.Example (old new identify original)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted)
open Reindex.Guarded.Institution (AdmittedAt Generated Valuation)
open Weakening.Guarded.Example (capture captureWidth)

abbrev finalSignature := insertSignature new capture 1

def insertion : Embedding new finalSignature := insert new capture 1

def input (fresh : Word captureWidth) (route : Bool) : Valuation finalSignature :=
  insertValue capture 1 fresh (Identification.Example.input 7 route)

def staged : Except Refusal (Generated finalSignature width) := do
  let source ← original.mapError Refusal.checker
  compileStaged identify insertion source

def direct : Except Refusal (Generated finalSignature width) := do
  let source ← original.mapError Refusal.checker
  Identification.compile (thenMap identify insertion.portMap) source

def compared : Except Refused (Compared identify insertion width) := do
  let source ← original.mapError (fun reason => Refused.staged (.checker reason))
  compare identify insertion source

def refusal (admission : Except SCCP.Dispatch.Refusal (AdmittedAt old width)) : Option Refusal :=
  admission.toOption.bind fun source =>
    match compileStaged identify insertion source with
    | .ok _ => none
    | .error reason => some reason

/-- Native, CF and numbered return words, with each run's own budget. -/
def run (compiled : Except Refusal (Generated finalSignature width)) (fresh : Word captureWidth)
    (route : Bool) : Option (Option Nat × Option Nat × Option Nat) := do
  let program ← compiled.toOption
  let values := input fresh route
  let source := @Admitted.source _ _ finalSignature.bankEq program.source
  return ((source.source.runFrom model 5 0 values).map BitVec.toNat,
    (program.artifacts.cf.run evalOp (if route then 6 else 7) (encodeValues values)).map
      (fun env => (env.get .here).toNat),
    (program.artifacts.numbered.2.run (Join.model model) 1 values).map
      (fun packet => (packet.get .head).toNat))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Example
