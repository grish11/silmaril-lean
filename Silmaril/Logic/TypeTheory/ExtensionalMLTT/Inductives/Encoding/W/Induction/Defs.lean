module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Fibres.Reconstruction.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- Canonical original fibre value over the raw tree's actual root. -/
def Description.canonical {k : ℕ} (S : Description) (t c : Tm k) : Tm k :=
  .pair t (.pair (.refl (S.root t)) c)

/-- A fully dependent indexed motive, expressed as an actual object function. -/
def Description.motiveType (S : Description) (n m : ℕ) : Tm 0 :=
  .pi S.index (.pi (S.fibreAt n (.bv 0)) (.univ m))

/-- The ordinary W motive quantifies the original coherence witness of its raw tree. -/
def Description.inductionMotive (S : Description) (n : ℕ) (C : Tm 0) : Tm 1 :=
  .pi (S.coherence n (.bv 0))
    (.app (.app (C.castLE (Nat.zero_le 2)) (S.root (.bv 1))) (S.canonical (.bv 1) (.bv 0)))

/-- The original node template under an arbitrary surrounding bound scope. -/
def Description.nodeAt {k : ℕ} (S : Description) (i a f : Tm k) : Tm k :=
  .pair (.sup (S.totalShape.castLE (Nat.zero_le k))
      (S.positions.castLE (Nat.succ_le_succ (Nat.zero_le k))) (.pair i a)
      (.abs (S.position.bsubst (Fin.cases a (fun _ => i))) (.fst (.app f.wk0 (.bv 0)))))
    (.pair (.refl i)
      (.abs (S.position.bsubst (Fin.cases a (fun _ => i))) (.snd (.app f.wk0 (.bv 0)))))

/-- The ordinary indexed dependent step: full original child fibres and their motive values. -/
def Description.indexedStepType (S : Description) (n : ℕ) (C : Tm 0) : Tm 0 :=
  .pi S.index (.pi S.shape
    (.pi (.pi S.position (S.fibreAt n S.next))
      (.pi (.pi S.position.wk0
        (.app (.app (C.castLE (Nat.zero_le 4)) (S.next.wkn 1)) (.app (.bv 1) (.bv 0))))
        (.app (.app (C.castLE (Nat.zero_le 4)) (.bv 3)) (S.nodeAt (.bv 3) (.bv 2) (.bv 1))))))

/-- The simultaneous method after its paired-index argument: shape, children and IHs. -/
def Description.indexedStepBody (S : Description) (n : ℕ) (C : Tm 0) : Tm 1 :=
  .pi S.shape
    (.pi (.pi S.position (S.fibreAt n S.next))
      (.pi (.pi S.position.wk0
        (.app (.app (C.castLE (Nat.zero_le 4)) (S.next.wkn 1)) (.app (.bv 1) (.bv 0))))
        (.app (.app (C.castLE (Nat.zero_le 4)) (.bv 3)) (S.nodeAt (.bv 3) (.bv 2) (.bv 1)))))

theorem Description.indexedStepType_eq (S : Description) (n : ℕ) (C : Tm 0) :
    S.indexedStepType n C = .pi S.index (S.indexedStepBody n C) := rfl

/-- Four actual source binders around a body scoped over index, shape, children and IHs. -/
def Description.indexedStepAbstraction (S : Description) (n : ℕ) (C : Tm 0) (b : Tm 4) : Tm 0 :=
  .abs S.index (.abs S.shape
    (.abs (.pi S.position (S.fibreAt n S.next))
      (.abs (.pi S.position.wk0
        (.app (.app (C.castLE (Nat.zero_le 4)) (S.next.wkn 1)) (.app (.bv 1) (.bv 0)))) b)))

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
