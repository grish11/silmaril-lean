module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Node.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.HypotheticalExamples

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

private theorem sourceShape : Ctx.nil.JEqB 2 (ContextClosure basis)
    (nullaryDescription.shape.lst .star) .star .star := by
  simpa only [nullaryDescription, Tm.lst] using
    (Ctx.JEqB.nil_ok (levels := 2) (H := ContextClosure basis))

private theorem sourceChildren : Ctx.nil.JEqB 2 (ContextClosure basis)
    (.pi (nullaryDescription.positionAt .star .star)
      (nullaryDescription.childFibres 0 (.pair .star .star))) nullaryChildren nullaryChildren :=
  WEncoding.Terms.nullaryChildren_typing.mono (Set.empty_subset _)

/-- The hypothesis-bearing original descriptor introduces an inhabitant of its exact indexed fibre. -/
theorem nullary_node_typing : Ctx.nil.JEqB 2 (ContextClosure basis) (nullaryDescription.fibre 0 .star)
    (nullaryDescription.node .star .star nullaryChildren)
    (nullaryDescription.node .star .star nullaryChildren) :=
  node_typing_of_hypotheses basis_structural nullarySourceData .nil_ok sourceShape sourceChildren

/-- The first projection is the original raw node, with the source child's original erasure. -/
theorem nullary_node_fst_beta : Ctx.nil.JEqB 2 (ContextClosure basis) nullaryDescription.raw
    (.fst (nullaryDescription.node .star .star nullaryChildren))
    (.sup nullaryDescription.totalShape nullaryDescription.positions (.pair .star .star)
      (.abs (nullaryDescription.positionAt .star .star) (.fst (.app nullaryChildren.wk0 (.bv 0))))) :=
  node_fst_beta_of_hypotheses basis_structural nullarySourceData .nil_ok sourceShape sourceChildren

/-- The original root equation and child-coherence function survive the second projection. -/
theorem nullary_node_snd_beta : Ctx.nil.JEqB 2 (ContextClosure basis)
    ((.sigma (.id nullaryDescription.index.wk0 (nullaryDescription.root (.bv 0)) Tm.star.wk0)
      (nullaryDescription.coherence 0 (.bv 1)) : Tm 1).lst
        (.sup nullaryDescription.totalShape nullaryDescription.positions (.pair .star .star)
          (.abs (nullaryDescription.positionAt .star .star) (.fst (.app nullaryChildren.wk0 (.bv 0))))))
    (.snd (nullaryDescription.node .star .star nullaryChildren))
    (.pair (.refl .star) (.abs (nullaryDescription.positionAt .star .star)
      (.snd (.app nullaryChildren.wk0 (.bv 0))))) :=
  node_snd_beta_of_hypotheses basis_structural nullarySourceData .nil_ok sourceShape sourceChildren

/-- Actual projection beta recovers the exact original coherence witness lambda. -/
theorem nullary_node_coherence_beta : Ctx.nil.JEqB 2 (ContextClosure basis)
    (nullaryDescription.coherence 0 (.sup nullaryDescription.totalShape nullaryDescription.positions
      (.pair .star .star) (.abs (nullaryDescription.positionAt .star .star)
        (.fst (.app nullaryChildren.wk0 (.bv 0))))))
    (.snd (.snd (nullaryDescription.node .star .star nullaryChildren)))
    (.abs (nullaryDescription.positionAt .star .star) (.snd (.app nullaryChildren.wk0 (.bv 0)))) :=
  node_coherence_beta_of_hypotheses basis_structural nullarySourceData .nil_ok sourceShape sourceChildren

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.HypotheticalExamples
