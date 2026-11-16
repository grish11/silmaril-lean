module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.RawStep.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- A normalized recursive call on the full original child under its position binder. -/
def Description.indexedHypothesisBody (S : Description) (n : ℕ) (C s g : Tm 0) : Tm 1 :=
  .app (.wrec S.totalShape.wk0 (S.positions.wkn 1) ((S.inductionMotive n C).wkn 1)
      (S.inductionStep n C s).wk0 (.fst (.app g.wk0 (.bv 0))))
    (.snd (.snd (.app g.wk0 (.bv 0))))

/-- The fully dependent source IH function consists of actual indexed recursive calls. -/
def Description.indexedHypotheses (S : Description) (n : ℕ) (C s i a g : Tm 0) : Tm 0 :=
  .abs (S.positionAt i a) (S.indexedHypothesisBody n C s g)

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
