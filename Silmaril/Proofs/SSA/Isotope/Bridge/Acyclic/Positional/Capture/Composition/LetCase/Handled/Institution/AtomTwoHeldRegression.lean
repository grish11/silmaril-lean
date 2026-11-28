module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation denoteRanked)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Slot Assembly)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
open scoped LetSeq.StraightLine.Structural Tagged

/-! ## Two tuples packed at once

There is one atom. `both` and `duo` take one atom and reply with a pair of
atoms. `trio` takes one atom and replies with a triple of atoms. `ping`
takes one atom and replies with one atom. `join` takes a pair of atoms and
replies with one atom. Every reply has one tag. Two older atoms are
captured. The exits are a pair of atoms and one atom. -/

private inductive Op | both | duo | trio | ping | join

local instance : TaggedSignature Unit Op where
  argument
    | .both => .atom ()
    | .duo => .atom ()
    | .trio => .atom ()
    | .ping => .atom ()
    | .join => .pair (.atom ()) (.atom ())
  first
    | .both => [(), ()]
    | .duo => [(), ()]
    | .trio => [(), (), ()]
    | .ping => [()]
    | .join => [()]
  others _ := []

private abbrev tok : Ty Unit := .base ()
private abbrev pairTy : Ty Unit := .product tok tok
private abbrev tripleTy : Ty Unit := .product tok pairTy
private abbrev older : BoundCtx (Ty Unit) 2 := (BoundCtx.snoc .nil tok).snoc tok
private abbrev Term (n : Nat) := LetCase.LocallyNameless.Tm Empty Op n

private theorem separable : Separable older := separable_atoms (.snoc (.snoc .nil ()) ())

private abbrev exits : List (Ty Unit) := [pairTy, tok]
private abbrev pairExit : ExitAt exits pairTy := .here

private abbrev earlier : Slot older tok := ⟨1, rfl⟩

/-! ## The chain

Ask `both` on the earlier capture and bind the pair. Hold it. Ask `duo` on
the later capture and keep its pair packed too. With both pairs packed, ask
`ping` on the earlier capture, with reply `c`. Destructure the pair of
`duo` into `x₁` and `x₂`. With the pair of `both` still packed, ask `join`
on a chosen atom and the earlier capture, with reply `d`. Then destructure
the pair of `both` into `a` and `b` and return a chosen pair. -/

/-- Under the held pair: the pair of `both` and the two captures. -/
private abbrev underPair : BoundCtx (Ty Unit) 3 := older.snoc pairTy
private abbrev laterUnder : Slot underPair tok := ⟨1, rfl⟩

/-- With both pairs packed: the pair of `duo`, the pair of `both` and the
two captures. Neither pair is an atom slot. -/
private abbrev bothPacked : BoundCtx (Ty Unit) 4 := underPair.snoc pairTy
private abbrev earlierPacked : Slot bothPacked tok := ⟨3, rfl⟩

/-- After the pair of `duo` is destructured: `x₂`, `x₁`, `c`, the pair of
`duo`, the pair of `both` and the two captures. -/
private abbrev freshOpen : BoundCtx (Ty Unit) 7 := ((bothPacked.snoc tok).snoc tok).snoc tok
private abbrev freshSecond : Slot freshOpen tok := ⟨0, rfl⟩
private abbrev freshFirst : Slot freshOpen tok := ⟨1, rfl⟩
private abbrev earlierOpen : Slot freshOpen tok := ⟨6, rfl⟩

/-- The leaf: `b`, `a`, `d`, `x₂`, `x₁`, `c`, the two pairs and the two
captures. -/
private abbrev leafCtx : BoundCtx (Ty Unit) 10 := ((freshOpen.snoc tok).snoc tok).snoc tok
private abbrev olderB : Slot leafCtx tok := ⟨0, rfl⟩
private abbrev olderA : Slot leafCtx tok := ⟨1, rfl⟩
private abbrev replyD : Slot leafCtx tok := ⟨2, rfl⟩
private abbrev leafSecond : Slot leafCtx tok := ⟨3, rfl⟩
private abbrev leafFirst : Slot leafCtx tok := ⟨4, rfl⟩
private abbrev earlierLeaf : Slot leafCtx tok := ⟨9, rfl⟩

/-- The tree with a chosen first argument of `join` and a chosen returned
pair. -/
private def chainWith (joined : Slot freshOpen tok) (first second : Slot leafCtx tok) :
    Spelled older exits
      (.let₁ (.op Op.both (.bv 1))
        (.let₁ (.op Op.duo (.bv 1))
          (.let₁ (.op Op.ping (.bv 3))
            (.let₂ (.bv 1)
              (.let₁ (.op Op.join (.pair (.bv joined.1) (.bv 6)))
                (.let₂ (.bv 5) (.inl (.pair (.bv first.1) (.bv second.1)))))))) : Term 2) :=
  .ask Op.both (.atom earlier)
    (.bind (.only [(), ()]
      (.hold [(), ()]
        (.ask Op.duo
          (.atom laterUnder)
          (.bind [(), ()]
            (.ask Op.ping
              (.atom earlierPacked)
              (.bind [()]
                (.atom
                  (.step
                    (.atom
                      (.ask Op.join
                        (.pair (.atom joined) (.atom earlierOpen))
                        (.bind [()]
                          (.atom
                            (.step (.atom (.done (.ret pairExit (.pair (.atom first) (.atom second)))))))))))))))))))

/-- The normal form with a chosen first argument of `join` and a chosen
returned pair. The pair of `both` is destructured before the chain and the
pair of `duo` right after `duo`. The four requests keep their order. -/
private abbrev normalWith (joined : Fin 9) (first second : Fin 10) : Term 2 :=
  .let₁ (.op Op.both (.bv 1))
    (.let₂ (.bv 0)
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.ping (.bv 7))
            (.let₁ (.op Op.join (.pair (.bv joined) (.bv 8)))
              (.inl (.pair (.bv first) (.bv second))))))))

/-- `join` takes the first atom of the pair of `duo` and the earlier
capture. The leaf uses both pairs after they are destructured: it returns
the first component of the pair of `both` with the second component of the
pair of `duo`. -/
private abbrev chain := chainWith freshFirst olderA leafSecond

/-- The spelled term. `ping` is asked while both pairs are packed. -/
example : Spelled older exits
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.duo (.bv 1))
        (.let₁ (.op Op.ping (.bv 3))
          (.let₂ (.bv 1)
            (.let₁ (.op Op.join (.pair (.bv 1) (.bv 6)))
              (.let₂ (.bv 5) (.inl (.pair (.bv 1) (.bv 3)))))))) : Term 2) := chain

/-- Its normal form. -/
private theorem chain_normal : (chain.normal (.id older)).1 = normalWith 2 6 2 := rfl

/-- The native equation between the spelling and its normal form. -/
example : Equiv false Γ₀ older
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.duo (.bv 1))
        (.let₁ (.op Op.ping (.bv 3))
          (.let₂ (.bv 1)
            (.let₁ (.op Op.join (.pair (.bv 1) (.bv 6)))
              (.let₂ (.bv 5) (.inl (.pair (.bv 1) (.bv 3)))))))) : Term 2)
    (.let₁ (.op Op.both (.bv 1))
      (.let₂ (.bv 0)
        (.let₁ (.op Op.duo (.bv 3))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.ping (.bv 7))
              (.let₁ (.op Op.join (.pair (.bv 2) (.bv 8)))
                (.inl (.pair (.bv 6) (.bv 2)))))))))
    (packedExitType exits) :=
  spelled_equiv_normal chain

/-- In a larger context the normal form is the renamed normal form. -/
example : (chain.normal (BoundCtx.Renaming.succ older tok)).1 =
    (normalWith 2 6 2).rename Fin.succ :=
  spelled_normal_rename_term chain (.id older) (BoundCtx.Renaming.succ older tok)

/-! ## Variants -/

/-- The other component of the pair of `both` is returned. -/
private abbrev otherOlder := chainWith freshFirst olderB leafSecond

/-- The other component of the pair of `duo` is returned. -/
private abbrev otherFresh := chainWith freshFirst olderA leafFirst

/-- `join` takes the second atom of the pair of `duo`. -/
private abbrev otherJoined := chainWith freshSecond olderA leafSecond

/-- The reply of `join` is returned in place of a component of the pair of
`duo`. -/
private abbrev replyReturned := chainWith freshFirst olderA replyD

/-- The earlier capture is returned in place of a component of the pair of
`duo`. -/
private abbrev withCapture := chainWith freshFirst olderA earlierLeaf

/-- The two returned atoms are exchanged. -/
private abbrev otherOrder := chainWith freshFirst leafSecond olderA

example : (otherOlder.normal (.id older)).1 = normalWith 2 5 2 := rfl
example : (otherFresh.normal (.id older)).1 = normalWith 2 6 3 := rfl
example : (otherJoined.normal (.id older)).1 = normalWith 1 6 2 := rfl
example : (replyReturned.normal (.id older)).1 = normalWith 2 6 0 := rfl
example : (withCapture.normal (.id older)).1 = normalWith 2 6 9 := rfl
example : (otherOrder.normal (.id older)).1 = normalWith 2 2 6 := rfl

/-- The contexts of the eager spelling. -/
private abbrev opened : BoundCtx (Ty Unit) 5 := ((older.snoc pairTy).snoc tok).snoc tok
private abbrev openedDuo : BoundCtx (Ty Unit) 8 := ((opened.snoc pairTy).snoc tok).snoc tok
private abbrev openedPing : BoundCtx (Ty Unit) 9 := openedDuo.snoc tok
private abbrev openedJoin : BoundCtx (Ty Unit) 10 := openedPing.snoc tok

private def eagerLeaf :=
  Spelled.ret (Φ := Op) (β := openedJoin) pairExit (.pair (.atom ⟨6, rfl⟩) (.atom ⟨2, rfl⟩))

private def eagerJoin :=
  Spelled.ask Op.join (.pair (.atom (β := openedPing) ⟨2, rfl⟩) (.atom ⟨8, rfl⟩))
    (.bind (.only [()] (.atom () eagerLeaf)))

private def eagerPing :=
  Spelled.ask Op.ping (.atom (β := openedDuo) ⟨7, rfl⟩) (.bind (.only [()] (.atom () eagerJoin)))

private def eagerDuo :=
  Spelled.ask Op.duo (.atom (β := opened) ⟨3, rfl⟩)
    (.bind (.only [(), ()] (.pair () () [] (.atom () eagerPing))))

/-- The eager spelling: each pair is destructured as soon as it is bound.
It is the normal form of the chain. -/
private def eager : Spelled older exits (normalWith 2 6 2) :=
  .ask Op.both (.atom earlier) (.bind (.only [(), ()] (.pair () () [] (.atom () eagerDuo))))

private theorem eager_normal : (eager.normal (.id older)).1 = normalWith 2 6 2 := rfl

/-! ## A triple kept packed under a held pair

Ask `both` and hold its pair. Ask `trio` and keep its triple packed. With
both packed, ask `ping` on the earlier capture. Destructure the triple
completely, then the pair, and return the second component of the pair
with the second atom of the triple. The length of the kept tuple is not
special. -/

private abbrev triplePacked : BoundCtx (Ty Unit) 4 := underPair.snoc tripleTy

private abbrev tripleLeaf : BoundCtx (Ty Unit) 11 :=
  ((((((triplePacked.snoc tok).snoc tok).snoc pairTy).snoc tok).snoc tok).snoc tok).snoc tok

private def tripleKept : Spelled older exits
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.trio (.bv 1))
        (.let₁ (.op Op.ping (.bv 3))
          (.let₂ (.bv 1)
            (.let₂ (.bv 0)
              (.let₂ (.bv 6) (.inl (.pair (.bv 0) (.bv 3)))))))) : Term 2) :=
  .ask Op.both (.atom earlier)
    (.bind (.only [(), ()]
      (.hold [(), ()]
        (.ask Op.trio
          (.atom laterUnder)
          (.bind [(), (), ()]
            (.ask Op.ping
              (.atom (β := triplePacked) ⟨3, rfl⟩)
              (.bind [()]
                (.atom
                  (.step
                    (.step
                      (.atom
                        (.step
                          (.atom
                            (.done
                              (.ret pairExit
                                (.pair (.atom (β := tripleLeaf) ⟨0, rfl⟩) (.atom ⟨3, rfl⟩)))))))))))))))))

/-- The pair is destructured before the chain and the triple right after
`trio`. -/
example : (tripleKept.normal (.id older)).1 =
    (.let₁ (.op Op.both (.bv 1))
      (.let₂ (.bv 0)
        (.let₁ (.op Op.trio (.bv 3))
          (.let₂ (.bv 0)
            (.let₂ (.bv 0)
              (.let₁ (.op Op.ping (.bv 9))
                (.inl (.pair (.bv 6) (.bv 2)))))))) : Term 2) := rfl

/-! ## Ranked validity and ordered-exit arrows -/

private abbrev sentence {t u : Term 2} (p : Spelled older exits t) (q : Spelled older exits u) :
    RankedEquation (atomSig Unit Op) :=
  sentenceOf (entryOf p.graph) (entryOf q.graph)

/-- The chain and the eager spelling are one sentence. -/
private theorem chain_eager : RankedValid false (sentence chain eager) :=
  (rankedValid_spelledTree_iff separable chain eager).mpr (chain_normal.trans eager_normal.symm)

/-- They have the same ordered-exit arrow at the ordered trace model with
atoms. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) =
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf eager.graph) :=
  (denoteRanked_spelledTree_iff separable chain eager).mpr (chain_normal.trans eager_normal.symm)

/-- Which component of the older pair is returned. -/
private theorem older_apart : ¬ RankedValid false (sentence chain otherOlder) := fun valid => by
  have same : normalWith 2 6 2 = normalWith 2 5 2 :=
    (rankedValid_spelledTree_iff separable chain otherOlder).mp valid
  simp at same

/-- Which component of the fresh pair is returned. -/
private theorem fresh_apart : ¬ RankedValid false (sentence chain otherFresh) := fun valid => by
  have same : normalWith 2 6 2 = normalWith 2 6 3 :=
    (rankedValid_spelledTree_iff separable chain otherFresh).mp valid
  simp at same

/-- Which component of the fresh pair the following request takes. -/
example : ¬ RankedValid false (sentence chain otherJoined) := fun valid => by
  have same : normalWith 2 6 2 = normalWith 1 6 2 :=
    (rankedValid_spelledTree_iff separable chain otherJoined).mp valid
  simp at same

/-- A component of the fresh pair and the reply of the following request. -/
example : ¬ RankedValid false (sentence chain replyReturned) := fun valid => by
  have same : normalWith 2 6 2 = normalWith 2 6 0 :=
    (rankedValid_spelledTree_iff separable chain replyReturned).mp valid
  simp at same

/-- A component of the fresh pair and an older capture. -/
example : ¬ RankedValid false (sentence chain withCapture) := fun valid => by
  have same : normalWith 2 6 2 = normalWith 2 6 9 :=
    (rankedValid_spelledTree_iff separable chain withCapture).mp valid
  simp at same

/-- The two pairs are told apart: exchanging the returned components. -/
example : ¬ RankedValid false (sentence chain otherOrder) := fun valid => by
  have same : normalWith 2 6 2 = normalWith 2 2 6 :=
    (rankedValid_spelledTree_iff separable chain otherOrder).mp valid
  simp at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms,
and the model rejects each sentence. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf otherOlder.graph) :=
  fun same => by
    have terms : normalWith 2 6 2 = normalWith 2 5 2 :=
      (denoteRanked_spelledTree_iff separable chain otherOlder).mp same
    simp at terms

example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf otherFresh.graph) :=
  fun same => by
    have terms : normalWith 2 6 2 = normalWith 2 6 3 :=
      (denoteRanked_spelledTree_iff separable chain otherFresh).mp same
    simp at terms

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain otherOlder) := fun holds =>
  older_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf otherOlder.graph) (spelled_graph chain) (spelled_graph otherOlder)).mpr holds)

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain otherFresh) := fun holds =>
  fresh_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf otherFresh.graph) (spelled_graph chain) (spelled_graph otherFresh)).mpr holds)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
