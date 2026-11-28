module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition

open SeaOfNodes.MLIR (Word)
open Example (first second liftValues naiveSucceeds compared compilerRefusal run)
open Factorization.Example (oldInput fill finalSignature)
open Identification.Example (lhs rhs old)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Backend Sentence)
open Reindex.Guarded.Institution (Valuation)

#guard liftValues 7 0 == some (7, 0)
#guard liftValues 7 65535 == some (7, 65535)
#guard liftValues 8 65535 == none
#guard !naiveSucceeds
#guard compared.isSome
#guard compilerRefusal == some (.first (.checker .neitherMarked))
#guard run 0 true == some ((some 99, some 99), (some 99, some 99), (some 99, some 99))
#guard run 65535 true == some ((some 99, some 99), (some 99, some 99), (some 99, some 99))
#guard run 65535 false == some ((some 14, some 14), (some 14, some 14), (some 14, some 14))

example : slot lhs ≠ slot rhs := by decide

example : first _ lhs = first _ rhs := rfl

example : second _ lhs = second _ rhs := rfl

example : ¬ ∃ target, Identification.reduct (Composition.thenMap first second) target = oldInput 8 true := by
  rintro ⟨target, reduced⟩
  have same := Identification.reduct_identifies (Composition.thenMap first second) target lhs rhs rfl
  rw [reduced] at same
  exact (show (7 : Word width) ≠ 8 by decide) same

example (side : Bool) (a b : Compared first second width) (m₁ m₂ : Valuation old)
    (u₁ u₂ : Valuation finalSignature)
    (left : liftStaged first second (oldInput 7 side) (fill 0) = some (m₁, u₁))
    (right : liftStaged first second (oldInput 7 side) (fill 65535) = some (m₂, u₂)) :
    ((Sentence.equation a b).map Compared.staged).Holds (fun q => Backend.cf.observe q.artifacts u₁) ↔
      ((Sentence.equation a b).map Compared.direct).Holds (fun q => Backend.petri.observe q.artifacts u₂) :=
  satisfaction_coherent left right .cf .petri (.equation a b)

example (q : Compared first second width) (mid : Valuation old) (target : Valuation finalSignature)
    (lifted : liftStaged first second (oldInput 7 false) (fill 0) = some (mid, target)) :
    (Sentence.terminates q.staged).Holds (fun a => Backend.numbered.observe a.artifacts target) ↔
      (Sentence.terminates q.intermediate).Holds (fun a => Backend.numbered.observe a.artifacts mid) :=
  (satisfaction_at_lift lifted .numbered (.terminates q)).1

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition
