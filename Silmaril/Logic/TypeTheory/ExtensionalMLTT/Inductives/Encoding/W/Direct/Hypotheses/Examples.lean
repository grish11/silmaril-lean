module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Direct.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.HypotheticalExamples

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- The original next term computes to successor of zero under actual nonempty source hypotheses. -/
theorem successor_direct_typing : Ctx.nil.JEqB 2 (ContextClosure basis) .nats (.succ .zero) (.succ .zero) := by
  have hi : Ctx.nil.JEqB 2 (ContextClosure basis) successorDescription.index .zero .zero := .zero .nil_ok
  have ha : Ctx.nil.JEqB 2 (ContextClosure basis) (successorDescription.shape.lst .zero) .star .star := by
    simpa only [successorDescription, Tm.lst] using (Ctx.JEqB.nil_ok (levels := 2) (H := ContextClosure basis))
  have hp : Ctx.nil.JEqB 2 (ContextClosure basis) (successorDescription.positionAt .zero .star) .star .star := by
    simpa only [successorDescription, Description.positionAt, Tm.bsubst] using
      (Ctx.JEqB.nil_ok (levels := 2) (H := ContextClosure basis))
  exact nextDirect_typing_of_hypotheses basis_structural successorSourceData hi ha hp

/-- The direct child index is typed from the actual label and original position value. -/
theorem successor_child_typing : Ctx.nil.JEqB 2 (ContextClosure basis) .nats
    (successorDescription.childIndexAt (.pair .zero .star) .star)
    (successorDescription.childIndexAt (.pair .zero .star) .star) := by
  have hl : Ctx.nil.JEqB 2 (ContextClosure basis) successorDescription.totalShape
      (.pair .zero .star) (.pair .zero .star) := by
    simpa only [successorDescription, Description.totalShape] using pair_instantiated
  have hp : Ctx.nil.JEqB 2 (ContextClosure basis)
      (successorDescription.positions.lst (.pair .zero .star)) .star .star := by
    simpa only [successorDescription, Description.positions, Tm.bsubst, Tm.lst] using
      (Ctx.JEqB.nil_ok (levels := 2) (H := ContextClosure basis))
  exact childIndexAt_typing_of_hypotheses basis_structural successorSourceData hl hp

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.HypotheticalExamples
