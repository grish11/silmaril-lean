module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.Motive.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- Reconstruct full original child values from raw children and original node coherence. -/
def Description.reifyChildren {k : ℕ} (S : Description) (l f c : Tm k) : Tm k :=
  .abs (S.position.bsubst (Fin.cases (.snd l) (fun _ => .fst l)))
    (.pair (.app f.wk0 (.bv 0)) (.app c.wk0 (.bv 0)))

/-- Feed each child's actual coherence to the ordinary recursive hypothesis. -/
def Description.reifyHypotheses {k : ℕ} (S : Description) (l c r : Tm k) : Tm k :=
  .abs (S.position.bsubst (Fin.cases (.snd l) (fun _ => .fst l)))
    (.app (.app r.wk0 (.bv 0)) (.snd (.app c.wk0 (.bv 0))))

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
