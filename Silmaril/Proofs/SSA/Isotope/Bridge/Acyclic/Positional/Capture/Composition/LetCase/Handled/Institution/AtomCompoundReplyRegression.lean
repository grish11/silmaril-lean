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

/-! ## A held tuple across a request with a compound reply

There is one atom. `both` takes one atom and replies with a pair of atoms.
`duo` takes one atom and replies with a pair of atoms. `trio` takes one
atom and replies with a triple of atoms. `join` takes a pair of atoms and
replies with one atom. Every reply has one tag. Two older atoms are
captured. The exits are a pair of atoms and one atom. -/

private inductive Op | both | duo | trio | join

local instance : TaggedSignature Unit Op where
  argument
    | .both => .atom ()
    | .duo => .atom ()
    | .trio => .atom ()
    | .join => .pair (.atom ()) (.atom ())
  first
    | .both => [(), ()]
    | .duo => [(), ()]
    | .trio => [(), (), ()]
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
the later capture, bind its reply and unpack it into `x₁` and `x₂`. Ask
`join` on a chosen atom and the earlier capture, with reply `c`. Then
destructure the held pair into `a` and `b` and return a chosen pair. -/

/-- Under the held pair: the pair and the two captures. -/
private abbrev underPair : BoundCtx (Ty Unit) 3 := older.snoc pairTy
private abbrev laterUnder : Slot underPair tok := ⟨1, rfl⟩

/-- After `duo` and the unpacking of its reply: `x₂`, `x₁`, the reply, the
held pair and the two captures. -/
private abbrev afterDuo : BoundCtx (Ty Unit) 6 := ((underPair.snoc pairTy).snoc tok).snoc tok
private abbrev freshSecond : Slot afterDuo tok := ⟨0, rfl⟩
private abbrev freshFirst : Slot afterDuo tok := ⟨1, rfl⟩
private abbrev laterAfterDuo : Slot afterDuo tok := ⟨4, rfl⟩
private abbrev earlierAfterDuo : Slot afterDuo tok := ⟨5, rfl⟩

/-- After the destructuring of the held pair: `b`, `a`, `c`, `x₂`, `x₁`,
the reply of `duo`, the held pair and the two captures. -/
private abbrev leafCtx : BoundCtx (Ty Unit) 9 := ((afterDuo.snoc tok).snoc tok).snoc tok
private abbrev compB : Slot leafCtx tok := ⟨0, rfl⟩
private abbrev compA : Slot leafCtx tok := ⟨1, rfl⟩
private abbrev replyC : Slot leafCtx tok := ⟨2, rfl⟩
private abbrev leafSecond : Slot leafCtx tok := ⟨3, rfl⟩
private abbrev earlierLeaf : Slot leafCtx tok := ⟨8, rfl⟩

/-- The tree with a chosen first argument of `join` and a chosen returned
pair. -/
private def chainWith (joined : Slot afterDuo tok) (first second : Slot leafCtx tok) :
    Spelled older exits
      (.let₁ (.op Op.both (.bv 1))
        (.let₁ (.op Op.duo (.bv 1))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.join (.pair (.bv joined.1) (.bv 5)))
              (.let₂ (.bv 4) (.inl (.pair (.bv first.1) (.bv second.1))))))) : Term 2) :=
  .ask Op.both (.atom earlier)
    (.bind (.only [(), ()]
      (.hold [(), ()]
        (.ask Op.duo
          (.atom laterUnder)
          (.bind [(), ()]
            (.step
              (.atom
                (.ask Op.join
                  (.pair (.atom joined) (.atom earlierAfterDuo))
                  (.bind [()]
                    (.atom (.step (.atom (.done (.ret pairExit (.pair (.atom first) (.atom second))))))))))))))))

/-- The normal form with a chosen first argument of `join` and a chosen
returned pair. The held pair is destructured before the two requests, and
the reply of `duo` is unpacked right after `duo`. -/
private abbrev normalWith (joined : Fin 8) (first second : Fin 9) : Term 2 :=
  .let₁ (.op Op.both (.bv 1))
    (.let₂ (.bv 0)
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv joined) (.bv 7)))
            (.inl (.pair (.bv first) (.bv second)))))))

/-- `join` takes the first atom of the reply of `duo` and the earlier
capture, while the held pair is still one slot. The returned pair has the
first component of the held pair and the reply of `join`. -/
private abbrev chain := chainWith freshFirst compA replyC

/-- The spelled term. -/
example : Spelled older exits
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.duo (.bv 1))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.let₂ (.bv 4) (.inl (.pair (.bv 1) (.bv 2))))))) : Term 2) := chain

/-- Its normal form. The three requests each occur once, in the same
order. `join` still takes the first atom of the reply of `duo` and the
earlier capture. -/
private theorem chain_normal : (chain.normal (.id older)).1 = normalWith 1 5 0 := rfl

/-- The native equation between the spelling and its normal form. -/
example : Equiv false Γ₀ older
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.duo (.bv 1))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.let₂ (.bv 4) (.inl (.pair (.bv 1) (.bv 2))))))) : Term 2)
    (.let₁ (.op Op.both (.bv 1))
      (.let₂ (.bv 0)
        (.let₁ (.op Op.duo (.bv 3))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.join (.pair (.bv 1) (.bv 7)))
              (.inl (.pair (.bv 5) (.bv 0))))))))
    (packedExitType exits) :=
  spelled_equiv_normal chain

/-- In a larger context the normal form is the renamed normal form. -/
example : (chain.normal (BoundCtx.Renaming.succ older tok)).1 =
    (normalWith 1 5 0).rename Fin.succ :=
  spelled_normal_rename_term chain (.id older) (BoundCtx.Renaming.succ older tok)

/-! ## Variants -/

/-- `join` takes the second atom of the reply of `duo`. -/
private abbrev otherFresh := chainWith freshSecond compA replyC

/-- `join` takes the later capture in place of an atom of the reply. -/
private abbrev captureJoined := chainWith laterAfterDuo compA replyC

/-- The other component of the held pair is returned. -/
private abbrev otherHeld := chainWith freshFirst compB replyC

/-- An atom of the reply of `duo` is returned in place of the reply of
`join`. -/
private abbrev freshReturned := chainWith freshFirst compA leafSecond

/-- The earlier capture is returned in place of the reply of `join`. -/
private abbrev withCapture := chainWith freshFirst compA earlierLeaf

/-- The two returned atoms are exchanged. -/
private abbrev otherOrder := chainWith freshFirst replyC compA

example : (otherFresh.normal (.id older)).1 = normalWith 0 5 0 := rfl
example : (captureJoined.normal (.id older)).1 = normalWith 6 5 0 := rfl
example : (otherHeld.normal (.id older)).1 = normalWith 1 4 0 := rfl
example : (freshReturned.normal (.id older)).1 = normalWith 1 5 1 := rfl
example : (withCapture.normal (.id older)).1 = normalWith 1 5 8 := rfl
example : (otherOrder.normal (.id older)).1 = normalWith 1 0 5 := rfl

/-- The contexts of the eager spelling: after the held pair is
destructured, after the reply of `duo` is unpacked, and after `join`. -/
private abbrev opened : BoundCtx (Ty Unit) 5 := ((older.snoc pairTy).snoc tok).snoc tok
private abbrev openedDuo : BoundCtx (Ty Unit) 8 := ((opened.snoc pairTy).snoc tok).snoc tok
private abbrev openedJoin : BoundCtx (Ty Unit) 9 := openedDuo.snoc tok

private def eagerLeaf :=
  Spelled.ret (Φ := Op) (β := openedJoin) pairExit (.pair (.atom ⟨5, rfl⟩) (.atom ⟨0, rfl⟩))

private def eagerJoin :=
  Spelled.ask Op.join (.pair (.atom (β := openedDuo) ⟨1, rfl⟩) (.atom ⟨7, rfl⟩))
    (.bind (.only [()] (.atom () eagerLeaf)))

private def eagerDuo :=
  Spelled.ask Op.duo (.atom (β := opened) ⟨3, rfl⟩)
    (.bind (.only [(), ()] (.pair () () [] (.atom () eagerJoin))))

/-- The eager spelling: destructure the held pair at once, then ask the
two requests. It is the normal form of the held chain. -/
private def eager : Spelled older exits (normalWith 1 5 0) :=
  .ask Op.both (.atom earlier) (.bind (.only [(), ()] (.pair () () [] (.atom () eagerDuo))))

private theorem eager_normal : (eager.normal (.id older)).1 = normalWith 1 5 0 := rfl

/-! ## A held triple across a request with a triple reply

Ask `trio` on the earlier capture and hold its triple. Ask `trio` on the
later capture, bind its reply and unpack it completely. Ask `join` on the
second atom of that reply and the earlier capture. Then unpack the held
triple and return its second atom with the reply of `join`. Neither tuple
length is special. -/

/-- Under the held triple. -/
private abbrev underTriple : BoundCtx (Ty Unit) 3 := older.snoc tripleTy

/-- After the second `trio` and the unpacking of its reply: `x₃`, `x₂`, the
rest of the reply, `x₁`, the reply, the held triple and the two captures. -/
private abbrev afterTrio : BoundCtx (Ty Unit) 8 :=
  ((((underTriple.snoc tripleTy).snoc tok).snoc pairTy).snoc tok).snoc tok

/-- After `join` and the unpacking of the held triple. -/
private abbrev tripleLeaf : BoundCtx (Ty Unit) 13 :=
  ((((afterTrio.snoc tok).snoc tok).snoc pairTy).snoc tok).snoc tok

private def triples : Spelled older exits
    (.let₁ (.op Op.trio (.bv 1))
      (.let₁ (.op Op.trio (.bv 1))
        (.let₂ (.bv 0)
          (.let₂ (.bv 0)
            (.let₁ (.op Op.join (.pair (.bv 1) (.bv 7)))
              (.let₂ (.bv 6)
                (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 4))))))))) : Term 2) :=
  .ask Op.trio (.atom earlier)
    (.bind (.only [(), (), ()]
      (.hold [(), (), ()]
        (.ask Op.trio
          (.atom (β := underTriple) ⟨1, rfl⟩)
          (.bind [(), (), ()]
            (.step
              (.step
                (.atom
                  (.ask Op.join
                    (.pair (.atom (β := afterTrio) ⟨1, rfl⟩) (.atom ⟨7, rfl⟩))
                    (.bind [()]
                      (.atom
                        (.step
                          (.step
                            (.atom
                              (.done
                                (.ret pairExit
                                  (.pair (.atom (β := tripleLeaf) ⟨1, rfl⟩) (.atom ⟨4, rfl⟩))))))))))))))))))

/-- The held triple is unpacked completely first, then the second `trio`
is asked and its reply unpacked, then `join`. -/
example : (triples.normal (.id older)).1 =
    (.let₁ (.op Op.trio (.bv 1))
      (.let₂ (.bv 0)
        (.let₂ (.bv 0)
          (.let₁ (.op Op.trio (.bv 5))
            (.let₂ (.bv 0)
              (.let₂ (.bv 0)
                (.let₁ (.op Op.join (.pair (.bv 1) (.bv 11)))
                  (.inl (.pair (.bv 7) (.bv 0))))))))) : Term 2) := rfl

/-! ## Ranked validity and ordered-exit arrows -/

private abbrev sentence {t u : Term 2} (p : Spelled older exits t) (q : Spelled older exits u) :
    RankedEquation (atomSig Unit Op) :=
  sentenceOf (entryOf p.graph) (entryOf q.graph)

example : (sentence chain eager).1.exits = [pairTy, tok] := rfl

/-- The held chain and the eager spelling are one sentence. -/
private theorem chain_eager : RankedValid false (sentence chain eager) :=
  (rankedValid_spelledTree_iff separable chain eager).mpr (chain_normal.trans eager_normal.symm)

/-- They have the same ordered-exit arrow at the ordered trace model with
atoms. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) =
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf eager.graph) :=
  (denoteRanked_spelledTree_iff separable chain eager).mpr (chain_normal.trans eager_normal.symm)

/-- Which atom of the compound reply the later request takes. -/
private theorem fresh_apart : ¬ RankedValid false (sentence chain otherFresh) := fun valid => by
  have same : normalWith 1 5 0 = normalWith 0 5 0 :=
    (rankedValid_spelledTree_iff separable chain otherFresh).mp valid
  simp at same

/-- An atom of the compound reply and an older capture, as the argument of
the later request. -/
example : ¬ RankedValid false (sentence chain captureJoined) := fun valid => by
  have same : normalWith 1 5 0 = normalWith 6 5 0 :=
    (rankedValid_spelledTree_iff separable chain captureJoined).mp valid
  simp at same

/-- Which component of the held pair is returned. -/
private theorem held_apart : ¬ RankedValid false (sentence chain otherHeld) := fun valid => by
  have same : normalWith 1 5 0 = normalWith 1 4 0 :=
    (rankedValid_spelledTree_iff separable chain otherHeld).mp valid
  simp at same

/-- The reply of the later request and an atom of the compound reply. -/
example : ¬ RankedValid false (sentence chain freshReturned) := fun valid => by
  have same : normalWith 1 5 0 = normalWith 1 5 1 :=
    (rankedValid_spelledTree_iff separable chain freshReturned).mp valid
  simp at same

/-- A reply of the chain and an older capture. -/
example : ¬ RankedValid false (sentence chain withCapture) := fun valid => by
  have same : normalWith 1 5 0 = normalWith 1 5 8 :=
    (rankedValid_spelledTree_iff separable chain withCapture).mp valid
  simp at same

/-- The order of the component and the reply. -/
example : ¬ RankedValid false (sentence chain otherOrder) := fun valid => by
  have same : normalWith 1 5 0 = normalWith 1 0 5 :=
    (rankedValid_spelledTree_iff separable chain otherOrder).mp valid
  simp at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms,
and the model rejects each sentence. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf otherHeld.graph) :=
  fun same => by
    have terms : normalWith 1 5 0 = normalWith 1 4 0 :=
      (denoteRanked_spelledTree_iff separable chain otherHeld).mp same
    simp at terms

example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf otherFresh.graph) :=
  fun same => by
    have terms : normalWith 1 5 0 = normalWith 0 5 0 :=
      (denoteRanked_spelledTree_iff separable chain otherFresh).mp same
    simp at terms

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain otherHeld) := fun holds =>
  held_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf otherHeld.graph) (spelled_graph chain) (spelled_graph otherHeld)).mpr holds)

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain otherFresh) := fun holds =>
  fresh_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf otherFresh.graph) (spelled_graph chain) (spelled_graph otherFresh)).mpr holds)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
