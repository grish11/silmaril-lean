module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Computation

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- The original fibre template under an arbitrary surrounding bound scope. -/
def Description.fibreAt {k : ℕ} (S : Description) (n : ℕ) (i : Tm k) : Tm k :=
  .sigma (S.raw.castLE (Nat.zero_le k))
    (.sigma (.id (S.index.castLE (Nat.zero_le _)) (S.root (.bv 0)) i.wk0)
      (S.coherence n (.bv 1)))

/-- Original fibres requested by the positions of an actual tagged label. -/
def Description.childFibres (S : Description) (n : ℕ) (l : Tm 0) : Tm 1 :=
  S.fibreAt n (S.childIndexAt l.wk0 (.bv 0))

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
