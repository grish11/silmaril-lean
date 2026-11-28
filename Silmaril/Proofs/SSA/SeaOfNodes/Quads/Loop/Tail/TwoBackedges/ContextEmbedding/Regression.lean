module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding

open CategoryTheory
open SeaOfNodes.Diamond (dataPorts)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (entry width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Backend Sentence)
open Reindex.Guarded.Institution (AdmittedAt Generated generatedRoom)
open Reindex.Guarded.Institution.Example (initialSignature original)
open Weakening.Guarded.Example (captureWidth)
open Example (first second alternate staged composed reordered route run input finalSignature)

#guard [staged, composed, reordered].all (fun compiled => route compiled == some true)
#guard [staged, composed, reordered].all (fun compiled =>
  run compiled 0 false true == some (some 99, some 99, some 99) &&
  run compiled 65535 true true == some (some 99, some 99, some 99))
#guard [staged, composed, reordered].all (fun compiled =>
  run compiled 0 false false == some (some 7, some 7, some 7) &&
  run compiled 65535 true false == some (some 7, some 7, some 7))

private theorem port_agreement (t : SeaOfNodes.Diamond.Ty Width)
    (port : Port (dataPorts initialSignature.regs) t) :
    (first.trans second).portMap t port = alternate.portMap t port := by
  cases port with
  | head => rfl
  | tail rest =>
    cases rest with
    | head => rfl
    | tail last =>
      cases last with
      | head => rfl
      | tail impossible => cases impossible

example (wide : Word captureWidth) (flag side : Bool) :
    (first.trans second).reduct (input wide flag side) = entry true side := rfl

private def middle := first.mapGenerated (Generated.lower original)
private def stagedTarget := second.mapGenerated (Generated.lower middle.source)
private def directTarget := (first.trans second).mapGenerated (Generated.lower original)
private def reorderedTarget := alternate.mapGenerated (Generated.lower original)

example (backend : Backend) (wide : Word captureWidth) (flag side : Bool) :
    backend.observe stagedTarget.artifacts (input wide flag side) =
      backend.observe directTarget.artifacts (input wide flag side) :=
  first.compile_staged second backend original (first.compile_eq original)
    (second.compile_eq middle.source) ((first.trans second).compile_eq original) (input wide flag side)

example (backend : Backend) (wide : Word captureWidth) (flag side : Bool) :
    backend.observe directTarget.artifacts (input wide flag side) =
      backend.observe reorderedTarget.artifacts (input wide flag side) :=
  (first.trans second).compile_congr alternate port_agreement backend original
    ((first.trans second).compile_eq original) (alternate.compile_eq original) (input wide flag side)

example (backend : Backend) (wide : Word captureWidth) (flag : Bool) :
    backend.Returns reorderedTarget.artifacts (input wide flag false) (7 : Word width) :=
  (alternate.compile_returns_iff backend original (alternate.compile_eq original) _ _).mpr
    ((@Backend.returns_iff_source _ _ initialSignature.bankEq backend original _ _).mpr ⟨5, rfl⟩)

example (backend : Backend) (wide : Word captureWidth) (flag side : Bool)
    (sentence : Sentence (Generated initialSignature width)) :
    (generatedRoom width backend finalSignature).Sat (Discrete.mk (input wide flag side))
      (((first.trans second).generatedCorridor backend).sen sentence) ↔
    (generatedRoom width backend finalSignature).Sat (Discrete.mk (input wide flag side))
      ((first.generatedCorridor backend ≫ second.generatedCorridor backend).sen sentence) := by
  rw [Embedding.generatedCorridor_trans]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding
