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

/-! ## A pair held across a chain of three requests

There is one atom. `both` takes one atom and replies with a pair of atoms.
`ping` takes one atom and replies with one atom. `join` takes a pair of
atoms and replies with one atom. `mark` takes one atom and replies with
nothing. Every reply has one tag. Two older atoms are captured. The exits
are a pair of atoms and one atom. -/

private inductive Op | both | ping | join | mark

local instance : TaggedSignature Unit Op where
  argument
    | .both => .atom ()
    | .ping => .atom ()
    | .join => .pair (.atom ()) (.atom ())
    | .mark => .atom ()
  first
    | .both => [(), ()]
    | .ping => [()]
    | .join => [()]
    | .mark => []
  others _ := []

private abbrev tok : Ty Unit := .base ()
private abbrev pairTy : Ty Unit := .product tok tok
private abbrev older : BoundCtx (Ty Unit) 2 := (BoundCtx.snoc .nil tok).snoc tok
private abbrev Term (n : Nat) := LetCase.LocallyNameless.Tm Empty Op n

private theorem separable : Separable older := separable_atoms (.snoc (.snoc .nil ()) ())

private abbrev exits : List (Ty Unit) := [pairTy, tok]
private abbrev pairExit : ExitAt exits pairTy := .here

private abbrev earlier : Slot older tok := ⟨1, rfl⟩

/-! ## The chain

Ask `both` on the earlier capture and bind the pair. Hold it. Ask `ping`
on the later capture, with reply `c₁`. Ask `join` on a chosen atom and the
earlier capture, with reply `c₂`. Ask `mark` on `c₂`. Then destructure the
pair into `a` and `b` and return a chosen pair. -/

/-- Under the held pair: the pair and the two captures. -/
private abbrev underPair : BoundCtx (Ty Unit) 3 := older.snoc pairTy
private abbrev laterUnder : Slot underPair tok := ⟨1, rfl⟩

/-- After `ping`: `c₁`, the pair and the two captures. -/
private abbrev afterPing : BoundCtx (Ty Unit) 4 := underPair.snoc tok
private abbrev firstReply : Slot afterPing tok := ⟨0, rfl⟩
private abbrev laterAfterPing : Slot afterPing tok := ⟨2, rfl⟩
private abbrev earlierAfterPing : Slot afterPing tok := ⟨3, rfl⟩

/-- After `join`: `c₂`, `c₁`, the pair and the two captures. -/
private abbrev afterJoin : BoundCtx (Ty Unit) 5 := afterPing.snoc tok
private abbrev secondReply : Slot afterJoin tok := ⟨0, rfl⟩

/-- After the destructuring: `b`, `a`, the reply of `mark`, `c₂`, `c₁`,
the pair and the two captures. -/
private abbrev leafCtx : BoundCtx (Ty Unit) 8 := (((afterJoin.snoc .unit).snoc tok).snoc tok)
private abbrev compB : Slot leafCtx tok := ⟨0, rfl⟩
private abbrev compA : Slot leafCtx tok := ⟨1, rfl⟩
private abbrev replyC2 : Slot leafCtx tok := ⟨3, rfl⟩
private abbrev replyC1 : Slot leafCtx tok := ⟨4, rfl⟩
private abbrev earlierLeaf : Slot leafCtx tok := ⟨7, rfl⟩

/-- The tree with a chosen first argument of `join` and a chosen returned
pair. -/
private def chainWith (joined : Slot afterPing tok) (first second : Slot leafCtx tok) :
    Spelled older exits
      (.let₁ (.op Op.both (.bv 1))
        (.let₁ (.op Op.ping (.bv 1))
          (.let₁ (.op Op.join (.pair (.bv joined.1) (.bv 3)))
            (.let₁ (.op Op.mark (.bv 0))
              (.let₂ (.bv 3) (.inl (.pair (.bv first.1) (.bv second.1))))))) : Term 2) :=
  .ask Op.both (.atom earlier)
    (.bind (.only [(), ()]
      (.hold [(), ()]
        (.ask Op.ping
          (.atom laterUnder)
          (.bind [()]
            (.atom
              (.ask Op.join
                (.pair (.atom joined) (.atom earlierAfterPing))
                (.bind [()]
                  (.atom
                    (.ask Op.mark
                      (.atom secondReply)
                      (.bind []
                        (.unit
                          (.step (.atom (.done (.ret pairExit (.pair (.atom first) (.atom second))))))))))))))))))

/-- The normal form with a chosen first argument of `join` and a chosen
returned pair. The pair is destructured before the three requests. -/
private abbrev normalWith (joined : Fin 6) (first second : Fin 8) : Term 2 :=
  .let₁ (.op Op.both (.bv 1))
    (.let₂ (.bv 0)
      (.let₁ (.op Op.ping (.bv 3))
        (.let₁ (.op Op.join (.pair (.bv joined) (.bv 5)))
          (.let₁ (.op Op.mark (.bv 0)) (.inl (.pair (.bv first) (.bv second)))))))

/-- `join` takes the reply of `ping`, so the second delayed request
depends on the first. The returned pair has the first component of the
held pair, bound after the chain, and the reply of `join`, bound before
the pair is destructured. -/
private abbrev chain := chainWith firstReply compA replyC2

/-- The spelled term: three requests are asked while the pair is one slot. -/
example : Spelled older exits
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.ping (.bv 1))
        (.let₁ (.op Op.join (.pair (.bv 0) (.bv 3)))
          (.let₁ (.op Op.mark (.bv 0))
            (.let₂ (.bv 3) (.inl (.pair (.bv 1) (.bv 3))))))) : Term 2) := chain

/-- Its normal form. The four requests each occur once, in the same
order. `join` still takes the reply of `ping` and the earlier capture, and
`mark` the reply of `join`. -/
example : (chain.normal (.id older)).1 = normalWith 0 4 1 := rfl

/-- The native equation between the spelling and its normal form. -/
example : Equiv false Γ₀ older
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.ping (.bv 1))
        (.let₁ (.op Op.join (.pair (.bv 0) (.bv 3)))
          (.let₁ (.op Op.mark (.bv 0))
            (.let₂ (.bv 3) (.inl (.pair (.bv 1) (.bv 3))))))) : Term 2)
    (.let₁ (.op Op.both (.bv 1))
      (.let₂ (.bv 0)
        (.let₁ (.op Op.ping (.bv 3))
          (.let₁ (.op Op.join (.pair (.bv 0) (.bv 5)))
            (.let₁ (.op Op.mark (.bv 0)) (.inl (.pair (.bv 4) (.bv 1))))))))
    (packedExitType exits) :=
  spelled_equiv_normal chain

/-! ## Variants -/

/-- `join` takes the later capture in place of the reply of `ping`. -/
private abbrev independent := chainWith laterAfterPing compA replyC2

/-- The other component of the held pair is returned. -/
private abbrev otherComponent := chainWith firstReply compB replyC2

/-- The reply of `ping` is returned in place of the reply of `join`. -/
private abbrev otherReply := chainWith firstReply compA replyC1

/-- The two returned atoms are exchanged. -/
private abbrev otherOrder := chainWith firstReply replyC2 compA

/-- The earlier capture is returned in place of the reply of `join`. -/
private abbrev withCapture := chainWith firstReply compA earlierLeaf

example : (independent.normal (.id older)).1 = normalWith 4 4 1 := rfl
example : (otherComponent.normal (.id older)).1 = normalWith 0 3 1 := rfl
example : (otherReply.normal (.id older)).1 = normalWith 0 4 2 := rfl
example : (otherOrder.normal (.id older)).1 = normalWith 0 1 4 := rfl
example : (withCapture.normal (.id older)).1 = normalWith 0 4 7 := rfl

/-- The contexts of the eager spelling: after the pair is destructured,
and after each of the three replies. -/
private abbrev opened : BoundCtx (Ty Unit) 5 := ((older.snoc pairTy).snoc tok).snoc tok
private abbrev openedPing : BoundCtx (Ty Unit) 6 := opened.snoc tok
private abbrev openedJoin : BoundCtx (Ty Unit) 7 := openedPing.snoc tok
private abbrev openedMark : BoundCtx (Ty Unit) 8 := openedJoin.snoc .unit

private def eagerLeaf :=
  Spelled.ret (Φ := Op) (β := openedMark) pairExit (.pair (.atom ⟨4, rfl⟩) (.atom ⟨1, rfl⟩))

private def eagerMark :=
  Spelled.ask Op.mark (.atom (β := openedJoin) ⟨0, rfl⟩) (.bind (.only [] (.unit eagerLeaf)))

private def eagerJoin :=
  Spelled.ask Op.join (.pair (.atom (β := openedPing) ⟨0, rfl⟩) (.atom ⟨5, rfl⟩))
    (.bind (.only [()] (.atom () eagerMark)))

private def eagerPing :=
  Spelled.ask Op.ping (.atom (β := opened) ⟨3, rfl⟩) (.bind (.only [()] (.atom () eagerJoin)))

/-- The eager spelling: destructure the pair at once, then ask the three
requests. It is the normal form of the held chain. -/
private def eager : Spelled older exits (normalWith 0 4 1) :=
  .ask Op.both (.atom earlier) (.bind (.only [(), ()] (.pair () () [] (.atom () eagerPing))))

example : (eager.normal (.id older)).1 = normalWith 0 4 1 := rfl

/-! ## Ranked validity and ordered-exit arrows -/

private abbrev sentence {t u : Term 2} (p : Spelled older exits t) (q : Spelled older exits u) :
    RankedEquation (atomSig Unit Op) :=
  sentenceOf (entryOf p.graph) (entryOf q.graph)

example : (sentence chain eager).1.exits = [pairTy, tok] := rfl

/-- The held chain and the eager spelling are one sentence. -/
private theorem chain_eager : RankedValid false (sentence chain eager) :=
  (rankedValid_spelledTree_iff separable chain eager).mpr rfl

/-- They have the same ordered-exit arrow at the ordered trace model with
atoms. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) =
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf eager.graph) :=
  (denoteRanked_spelledTree_iff separable chain eager).mpr rfl

/-- The dependency of the second delayed request on the first is observed. -/
private theorem dependency_apart : ¬ RankedValid false (sentence chain independent) := fun valid => by
  have same : normalWith 0 4 1 = normalWith 4 4 1 :=
    (rankedValid_spelledTree_iff separable chain independent).mp valid
  simp at same

/-- Which component of the held pair is returned. -/
example : ¬ RankedValid false (sentence chain otherComponent) := fun valid => by
  have same : normalWith 0 4 1 = normalWith 0 3 1 :=
    (rankedValid_spelledTree_iff separable chain otherComponent).mp valid
  simp at same

/-- Which reply of the chain is returned. -/
example : ¬ RankedValid false (sentence chain otherReply) := fun valid => by
  have same : normalWith 0 4 1 = normalWith 0 4 2 :=
    (rankedValid_spelledTree_iff separable chain otherReply).mp valid
  simp at same

/-- The order of the component and the reply. -/
example : ¬ RankedValid false (sentence chain otherOrder) := fun valid => by
  have same : normalWith 0 4 1 = normalWith 0 1 4 :=
    (rankedValid_spelledTree_iff separable chain otherOrder).mp valid
  simp at same

/-- A reply of the chain and an older capture. -/
example : ¬ RankedValid false (sentence chain withCapture) := fun valid => by
  have same : normalWith 0 4 1 = normalWith 0 4 7 :=
    (rankedValid_spelledTree_iff separable chain withCapture).mp valid
  simp at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms,
and the model rejects the sentence. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf independent.graph) :=
  fun same => by
    have terms : normalWith 0 4 1 = normalWith 4 4 1 :=
      (denoteRanked_spelledTree_iff separable chain independent).mp same
    simp at terms

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain independent) := fun holds =>
  dependency_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf independent.graph) (spelled_graph chain) (spelled_graph independent)).mpr holds)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
