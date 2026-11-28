module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded.Example.Defs

/-! Insert i16 and Boolean captures at distinct interior positions. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Example

open SeaOfNodes.Loop.MLIR.CF (model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open SCCP.Dispatch (Refusal)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted)
open Reindex.Guarded.Institution (Generated Valuation)
open Reindex.Guarded.Institution.Example (initialSignature original)
open Weakening.Guarded.Example (capture captureWidth)

abbrev middleSignature := insertSignature initialSignature capture 1
abbrev finalSignature := insertSignature middleSignature .predicate 3
abbrev otherMiddle := insertSignature initialSignature .predicate 2

def first : Embedding initialSignature middleSignature := insert initialSignature capture 1

def second : Embedding middleSignature finalSignature := insert middleSignature .predicate 3

/-- Insert the Bool first instead. The old register positions agree in the final bank. -/
def alternate : Embedding initialSignature finalSignature :=
  (insert initialSignature .predicate 2).trans (insert otherMiddle capture 1)

def staged : Except Refusal (Generated finalSignature width) := do
  let middle ← first.compile original
  second.compile middle.source

def composed : Except Refusal (Generated finalSignature width) :=
  (first.trans second).compile original

def reordered : Except Refusal (Generated finalSignature width) :=
  alternate.compile original

def input (wide : Word captureWidth) (flag side : Bool) : Valuation finalSignature :=
  .cons ⟨true⟩ (.cons wide (.cons ⟨side⟩ (.cons ⟨flag⟩ (.cons (7 : Word width) .nil))))

def route (compiled : Except Refusal (Generated finalSignature width)) : Option Bool :=
  compiled.toOption.map (fun program => selectedSide program.source)

/-- Run each actual artifact at its own bound on the same enlarged bank. -/
def run (compiled : Except Refusal (Generated finalSignature width))
    (wide : Word captureWidth) (flag side : Bool) : Option (Option Nat × Option Nat × Option Nat) := do
  let program ← compiled.toOption
  let values := input wide flag side
  let source := @Admitted.source _ _ finalSignature.bankEq program.source
  let cfFuel := if side then 6 else 7
  return ((source.source.runFrom model 5 0 values).map BitVec.toNat,
    (program.artifacts.cf.run evalOp cfFuel (encodeValues values)).map (fun env => (env.get .here).toNat),
    (program.artifacts.numbered.2.run (Join.model model) 1 values).map (fun packet => (packet.get .head).toNat))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Example
