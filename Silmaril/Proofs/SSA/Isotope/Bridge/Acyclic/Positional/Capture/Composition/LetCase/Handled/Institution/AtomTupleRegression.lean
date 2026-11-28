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

/-! ## A triple held across a chain of dependent requests

There is one atom. `trio` takes one atom and replies with a triple of
atoms. `ping` takes one atom and replies with one atom. `join` takes a
pair of atoms and replies with one atom. Every reply has one tag. Two
older atoms are captured. The exits are a pair of atoms and one atom. -/

private inductive Op | trio | ping | join

local instance : TaggedSignature Unit Op where
  argument
    | .trio => .atom ()
    | .ping => .atom ()
    | .join => .pair (.atom ()) (.atom ())
  first
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

Ask `trio` on the earlier capture and bind the triple. Hold it. Ask `ping`
on the later capture, with reply `c₁`. Ask `join` on a chosen atom and the
earlier capture, with reply `c₂`. Then destructure the triple into `a` and
the rest, destructure the rest into `b` and `c`, and return a chosen
pair. -/

/-- Under the held triple: the triple and the two captures. -/
private abbrev underTriple : BoundCtx (Ty Unit) 3 := older.snoc tripleTy
private abbrev laterUnder : Slot underTriple tok := ⟨1, rfl⟩

/-- After `ping`: `c₁`, the triple and the two captures. -/
private abbrev afterPing : BoundCtx (Ty Unit) 4 := underTriple.snoc tok
private abbrev firstReply : Slot afterPing tok := ⟨0, rfl⟩
private abbrev laterAfterPing : Slot afterPing tok := ⟨2, rfl⟩
private abbrev earlierAfterPing : Slot afterPing tok := ⟨3, rfl⟩

/-- After `join`: `c₂`, `c₁`, the triple and the two captures. -/
private abbrev afterJoin : BoundCtx (Ty Unit) 5 := afterPing.snoc tok

/-- After both destructurings: `c`, `b`, the rest of the triple, `a`,
`c₂`, `c₁`, the triple and the two captures. -/
private abbrev leafCtx : BoundCtx (Ty Unit) 9 := (((afterJoin.snoc tok).snoc pairTy).snoc tok).snoc tok
private abbrev compC : Slot leafCtx tok := ⟨0, rfl⟩
private abbrev compB : Slot leafCtx tok := ⟨1, rfl⟩
private abbrev compA : Slot leafCtx tok := ⟨3, rfl⟩
private abbrev replyC2 : Slot leafCtx tok := ⟨4, rfl⟩
private abbrev replyC1 : Slot leafCtx tok := ⟨5, rfl⟩
private abbrev earlierLeaf : Slot leafCtx tok := ⟨8, rfl⟩

/-- The tree with a chosen first argument of `join` and a chosen returned
pair. -/
private def chainWith (joined : Slot afterPing tok) (first second : Slot leafCtx tok) :
    Spelled older exits
      (.let₁ (.op Op.trio (.bv 1))
        (.let₁ (.op Op.ping (.bv 1))
          (.let₁ (.op Op.join (.pair (.bv joined.1) (.bv 3)))
            (.let₂ (.bv 2)
              (.let₂ (.bv 0) (.inl (.pair (.bv first.1) (.bv second.1))))))) : Term 2) :=
  .ask Op.trio (.atom earlier)
    (.bind (.only [(), (), ()]
      (.hold [(), (), ()]
        (.ask Op.ping
          (.atom laterUnder)
          (.bind [()]
            (.atom
              (.ask Op.join
                (.pair (.atom joined) (.atom earlierAfterPing))
                (.bind [()]
                  (.atom
                    (.step (.step (.atom (.done (.ret pairExit (.pair (.atom first) (.atom second))))))))))))))))

/-- The normal form with a chosen first argument of `join` and a chosen
returned pair. The triple is unpacked completely before the two requests. -/
private abbrev normalWith (joined : Fin 8) (first second : Fin 9) : Term 2 :=
  .let₁ (.op Op.trio (.bv 1))
    (.let₂ (.bv 0)
      (.let₂ (.bv 0)
        (.let₁ (.op Op.ping (.bv 5))
          (.let₁ (.op Op.join (.pair (.bv joined) (.bv 7)))
            (.inl (.pair (.bv first) (.bv second)))))))

/-- `join` takes the reply of `ping`, so the second delayed request
depends on the first. The returned pair has the inner component `b` of the
held triple, bound after the chain, and the reply of `join`, bound before
the triple is destructured. -/
private abbrev chain := chainWith firstReply compB replyC2

/-- The spelled term: two requests are asked while the triple is one slot. -/
example : Spelled older exits
    (.let₁ (.op Op.trio (.bv 1))
      (.let₁ (.op Op.ping (.bv 1))
        (.let₁ (.op Op.join (.pair (.bv 0) (.bv 3)))
          (.let₂ (.bv 2)
            (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 4))))))) : Term 2) := chain

/-- Its normal form. The three requests each occur once, in the same
order. `join` still takes the reply of `ping` and the earlier capture. -/
example : (chain.normal (.id older)).1 = normalWith 0 3 0 := rfl

/-- The native equation between the spelling and its normal form. -/
example : Equiv false Γ₀ older
    (.let₁ (.op Op.trio (.bv 1))
      (.let₁ (.op Op.ping (.bv 1))
        (.let₁ (.op Op.join (.pair (.bv 0) (.bv 3)))
          (.let₂ (.bv 2)
            (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 4))))))) : Term 2)
    (.let₁ (.op Op.trio (.bv 1))
      (.let₂ (.bv 0)
        (.let₂ (.bv 0)
          (.let₁ (.op Op.ping (.bv 5))
            (.let₁ (.op Op.join (.pair (.bv 0) (.bv 7)))
              (.inl (.pair (.bv 3) (.bv 0))))))))
    (packedExitType exits) :=
  spelled_equiv_normal chain

/-- In a larger context the normal form is the renamed normal form. -/
example : (chain.normal (BoundCtx.Renaming.succ older tok)).1 =
    (normalWith 0 3 0).rename Fin.succ :=
  spelled_normal_rename_term chain (.id older) (BoundCtx.Renaming.succ older tok)

/-! ## Variants -/

/-- `join` takes the later capture in place of the reply of `ping`. -/
private abbrev independent := chainWith laterAfterPing compB replyC2

/-- The other inner component of the held triple is returned. -/
private abbrev otherInner := chainWith firstReply compC replyC2

/-- The first component of the held triple is returned. -/
private abbrev firstComponent := chainWith firstReply compA replyC2

/-- The earlier capture is returned in place of the inner component. -/
private abbrev captureForInner := chainWith firstReply earlierLeaf replyC2

/-- The reply of `ping` is returned in place of the reply of `join`. -/
private abbrev otherReply := chainWith firstReply compB replyC1

/-- The two returned atoms are exchanged. -/
private abbrev otherOrder := chainWith firstReply replyC2 compB

/-- The earlier capture is returned in place of the reply of `join`. -/
private abbrev withCapture := chainWith firstReply compB earlierLeaf

example : (independent.normal (.id older)).1 = normalWith 6 3 0 := rfl
example : (otherInner.normal (.id older)).1 = normalWith 0 2 0 := rfl
example : (firstComponent.normal (.id older)).1 = normalWith 0 5 0 := rfl
example : (captureForInner.normal (.id older)).1 = normalWith 0 8 0 := rfl
example : (otherReply.normal (.id older)).1 = normalWith 0 3 1 := rfl
example : (otherOrder.normal (.id older)).1 = normalWith 0 0 3 := rfl
example : (withCapture.normal (.id older)).1 = normalWith 0 3 8 := rfl

/-- The contexts of the eager spelling: after the triple is unpacked, and
after each of the two replies. -/
private abbrev opened : BoundCtx (Ty Unit) 7 := ((((older.snoc tripleTy).snoc tok).snoc pairTy).snoc tok).snoc tok
private abbrev openedPing : BoundCtx (Ty Unit) 8 := opened.snoc tok
private abbrev openedJoin : BoundCtx (Ty Unit) 9 := openedPing.snoc tok

private def eagerLeaf :=
  Spelled.ret (Φ := Op) (β := openedJoin) pairExit (.pair (.atom ⟨3, rfl⟩) (.atom ⟨0, rfl⟩))

private def eagerJoin :=
  Spelled.ask Op.join (.pair (.atom (β := openedPing) ⟨0, rfl⟩) (.atom ⟨7, rfl⟩))
    (.bind (.only [()] (.atom () eagerLeaf)))

private def eagerPing :=
  Spelled.ask Op.ping (.atom (β := opened) ⟨5, rfl⟩) (.bind (.only [()] (.atom () eagerJoin)))

/-- The eager spelling: unpack the triple at once, then ask the two
requests. It is the normal form of the held chain. -/
private def eager : Spelled older exits (normalWith 0 3 0) :=
  .ask Op.trio (.atom earlier)
    (.bind (.only [(), (), ()] (.pair () () [()] (.pair () () [] (.atom () eagerPing)))))

example : (eager.normal (.id older)).1 = normalWith 0 3 0 := rfl

/-! ## The rest of the triple held again

After the first destructuring the rest of the triple is a pending pair. It
is held across a further request, which takes the first atom `a` of the
triple. -/

/-- After the first destructuring: the rest of the triple, `a`, `c₂`,
`c₁`, the triple and the two captures. -/
private abbrev afterFirst : BoundCtx (Ty Unit) 7 := (afterJoin.snoc tok).snoc pairTy
private abbrev firstAtom : Slot afterFirst tok := ⟨1, rfl⟩

/-- After the second chain and destructuring: `c`, `b`, the reply `c₃`,
the rest of the triple, `a`, `c₂`, `c₁`, the triple and the two captures. -/
private abbrev againLeaf : BoundCtx (Ty Unit) 10 := ((afterFirst.snoc tok).snoc tok).snoc tok

private def again : Spelled older exits
    (.let₁ (.op Op.trio (.bv 1))
      (.let₁ (.op Op.ping (.bv 1))
        (.let₁ (.op Op.join (.pair (.bv 0) (.bv 3)))
          (.let₂ (.bv 2)
            (.let₁ (.op Op.ping (.bv 1))
              (.let₂ (.bv 1) (.inl (.pair (.bv 1) (.bv 2)))))))) : Term 2) :=
  .ask Op.trio (.atom earlier)
    (.bind (.only [(), (), ()]
      (.hold [(), (), ()]
        (.ask Op.ping
          (.atom laterUnder)
          (.bind [()]
            (.atom
              (.ask Op.join
                (.pair (.atom firstReply) (.atom earlierAfterPing))
                (.bind [()]
                  (.atom
                    (.step
                      (.ask Op.ping
                        (.atom firstAtom)
                        (.bind [()]
                          (.atom
                            (.step
                              (.atom
                                (.done
                                  (.ret pairExit
                                    (.pair (.atom (β := againLeaf) ⟨1, rfl⟩) (.atom ⟨2, rfl⟩)))))))))))))))))))

/-- The triple is unpacked completely before the three requests. The
third request still takes the first atom of the triple. -/
example : (again.normal (.id older)).1 =
    (.let₁ (.op Op.trio (.bv 1))
      (.let₂ (.bv 0)
        (.let₂ (.bv 0)
          (.let₁ (.op Op.ping (.bv 5))
            (.let₁ (.op Op.join (.pair (.bv 0) (.bv 7)))
              (.let₁ (.op Op.ping (.bv 5))
                (.inl (.pair (.bv 4) (.bv 0)))))))) : Term 2) := rfl

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
  have same : normalWith 0 3 0 = normalWith 6 3 0 :=
    (rankedValid_spelledTree_iff separable chain independent).mp valid
  simp at same

/-- Which inner component of the held triple is returned. -/
private theorem inner_apart : ¬ RankedValid false (sentence chain otherInner) := fun valid => by
  have same : normalWith 0 3 0 = normalWith 0 2 0 :=
    (rankedValid_spelledTree_iff separable chain otherInner).mp valid
  simp at same

/-- The inner component and the first component. -/
example : ¬ RankedValid false (sentence chain firstComponent) := fun valid => by
  have same : normalWith 0 3 0 = normalWith 0 5 0 :=
    (rankedValid_spelledTree_iff separable chain firstComponent).mp valid
  simp at same

/-- The inner component and an older capture. -/
private theorem capture_apart : ¬ RankedValid false (sentence chain captureForInner) := fun valid => by
  have same : normalWith 0 3 0 = normalWith 0 8 0 :=
    (rankedValid_spelledTree_iff separable chain captureForInner).mp valid
  simp at same

/-- Which reply of the chain is returned. -/
example : ¬ RankedValid false (sentence chain otherReply) := fun valid => by
  have same : normalWith 0 3 0 = normalWith 0 3 1 :=
    (rankedValid_spelledTree_iff separable chain otherReply).mp valid
  simp at same

/-- The order of the component and the reply. -/
example : ¬ RankedValid false (sentence chain otherOrder) := fun valid => by
  have same : normalWith 0 3 0 = normalWith 0 0 3 :=
    (rankedValid_spelledTree_iff separable chain otherOrder).mp valid
  simp at same

/-- A reply of the chain and an older capture. -/
example : ¬ RankedValid false (sentence chain withCapture) := fun valid => by
  have same : normalWith 0 3 0 = normalWith 0 3 8 :=
    (rankedValid_spelledTree_iff separable chain withCapture).mp valid
  simp at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms,
and the model rejects each sentence. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf otherInner.graph) :=
  fun same => by
    have terms : normalWith 0 3 0 = normalWith 0 2 0 :=
      (denoteRanked_spelledTree_iff separable chain otherInner).mp same
    simp at terms

example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf captureForInner.graph) :=
  fun same => by
    have terms : normalWith 0 3 0 = normalWith 0 8 0 :=
      (denoteRanked_spelledTree_iff separable chain captureForInner).mp same
    simp at terms

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain otherInner) := fun holds =>
  inner_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf otherInner.graph) (spelled_graph chain) (spelled_graph otherInner)).mpr holds)

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain captureForInner) := fun holds =>
  capture_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf captureForInner.graph) (spelled_graph chain) (spelled_graph captureForInner)).mpr holds)

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain independent) := fun holds =>
  dependency_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf independent.graph) (spelled_graph chain) (spelled_graph independent)).mpr holds)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
