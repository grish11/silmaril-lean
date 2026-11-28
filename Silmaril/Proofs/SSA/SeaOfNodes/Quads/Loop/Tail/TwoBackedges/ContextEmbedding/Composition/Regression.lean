module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition

open SeaOfNodes.Loop.MLIR.CF (Op)
open SeaOfNodes.MLIR (Word)
open Identification.Example (identify lhs rhs output originalProgram conflicting changesAdmission)
open Example (finalSignature insertion input staged direct compared refusal run)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Backend Sentence)
open Weakening.Guarded.Example (captureWidth)

#guard compared.isOk
#guard run staged 0 true == some (some 99, some 99, some 99)
#guard run direct 65535 true == some (some 99, some 99, some 99)
#guard run staged 65535 false == some (some 14, some 14, some 14)
#guard run direct 0 false == some (some 14, some 14, some 14)

#guard refusal conflicting == some .incompatibleFacts
#guard refusal changesAdmission == some (.checker .neitherMarked)

private def combined := thenMap identify insertion.portMap

example : slot lhs ≠ slot rhs := by decide

example : (Identification.program combined originalProgram).preheader =
    ([⟨_, _, combined _ output, .arithmetic (.binary .addi),
      .cons (combined _ lhs) (.cons (combined _ lhs) .nil)⟩] : List (Quad Op finalSignature.regs)) := rfl

example (fresh : Word captureWidth) (route : Bool) :
    Identification.reduct combined (input fresh route) =
      Identification.reduct identify (Identification.Example.input 7 route) := by
  rw [combined, reduct_embedding identify insertion]
  exact congrArg (Identification.reduct identify) (reduct_insertValue ..)

example (pair : Compared identify insertion width) (backend : Backend) (fresh : Word captureWidth)
    (route : Bool) (word : Word width) :
    backend.Returns pair.staged.artifacts (input fresh route) word ↔
      backend.Returns pair.direct.artifacts (input fresh route) word :=
  pair.returns_iff backend (input fresh route) word

example (pair : Compared identify insertion width) (backend : Backend) (fresh : Word captureWidth)
    (route : Bool) :
    (Sentence.terminates pair.staged).Holds (fun q => backend.observe q.artifacts (input fresh route)) ↔
    (Sentence.terminates pair.direct).Holds (fun q => backend.observe q.artifacts (input fresh route)) :=
  Compared.satisfaction_iff backend (input fresh route) (.terminates pair)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition
