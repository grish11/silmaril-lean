module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.Step.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- Apply the supplied original indexed step to full reconstructed source data. -/
def Description.sourceStepValue {k : ℕ} (S : Description) (s l f c r : Tm k) : Tm k :=
  .app (.app (.app (.app s (.fst l)) (.snd l)) (S.reifyChildren l f c)) (S.reifyHypotheses l c r)

/-- Abstract the original coherence witness in the actual indexed source-step application. -/
def Description.coherentStep {k : ℕ} (S : Description) (n : ℕ) (s l f r : Tm k) : Tm k :=
  .abs (S.coherence n (.sup (S.totalShape.castLE (Nat.zero_le k))
      (S.positions.castLE (Nat.succ_le_succ (Nat.zero_le k))) l f))
    (S.sourceStepValue s.wk0 l.wk0 f.wk0 (.bv 0) r.wk0)

/-- Ordinary W step synthesized from the actual original indexed dependent step. -/
def Description.inductionStep (S : Description) (n : ℕ) (C s : Tm 0) : Tm 0 :=
  .abs S.totalShape (.abs (.pi S.positions (S.raw.castLE (Nat.zero_le 2)))
    (.abs (.pi (S.positions.bsubst (fun _ => .bv 1))
      ((S.inductionMotive n C).bsubst (fun _ => .app (.bv 1) (.bv 0))))
      (S.coherentStep n (s.castLE (Nat.zero_le 3)) (.bv 2) (.bv 1) (.bv 0))))

/-- Dependent elimination from the original encoded fibre, with its synthesized ordinary W step. -/
def Description.indexedInduction (S : Description) (n : ℕ) (C s t : Tm 0) : Tm 0 :=
  .app (.wrec S.totalShape S.positions (S.inductionMotive n C) (S.inductionStep n C s) (.fst t))
    (.snd (.snd t))

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
