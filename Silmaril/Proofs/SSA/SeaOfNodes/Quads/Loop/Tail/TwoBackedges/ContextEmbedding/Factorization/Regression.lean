module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization

open SeaOfNodes.MLIR (Word)
open Identification.Example (lhs rhs originalProgram)
open Factorization.Example (captureMap finalSignature keptSlots oldInput fill liftedGap compared run)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted Backend Sentence)
open Reindex.Guarded.Institution (Valuation)
open Weakening.Guarded.Example (captureWidth)

#guard keptSlots == [0, 2, 3, 4]
#guard Identification.checkWrites (compress captureMap) originalProgram
#guard compared.isSome
#guard liftedGap 7 65535 == some 65535
#guard liftedGap 7 0 == some 0
#guard liftedGap 8 0 == none
#guard run 65535 true == some ((some 99, some 99), (some 99, some 99))
#guard run 0 false == some ((some 14, some 14), (some 14, some 14))

example : slot lhs ≠ slot rhs := by decide

example : ¬ ∃ target, Identification.reduct captureMap target = oldInput 8 false := by
  intro existsTarget
  have consistent := (reduct_image_iff captureMap _).mp existsTarget
  have same := consistent _ lhs rhs rfl
  change (7 : Word width) = 8 at same
  exact (show (7 : Word width) ≠ 8 by decide) same

example (backend : Backend) (wide : Word captureWidth) (target : Valuation finalSignature)
    (lifted : liftChecked captureMap (oldInput 7 false) (fill wide) = some target)
    (sentence : Sentence (Compared captureMap width)) :
    (sentence.map Composition.Compared.direct).Holds (fun q => backend.observe q.artifacts target) ↔
      sentence.Holds (fun q => @Admitted.observe _ _ Identification.Example.old.bankEq q.source (oldInput 7 false)) :=
  direct_satisfaction_at_lift lifted backend sentence

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization
