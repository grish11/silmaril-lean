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

/-! ## A held tuple across a request with two tags

There is one atom. `both` takes one atom and replies with a pair of atoms.
`trio` takes one atom and replies with a triple of atoms. `pick` takes one
atom and replies with one of two tags: the first carries a pair of atoms
and the second one atom. `join` takes a pair of atoms and replies with one
atom. Two older atoms are captured. The exits are a pair of atoms and one
atom. -/

private inductive Op | both | trio | pick | join

local instance : TaggedSignature Unit Op where
  argument
    | .both => .atom ()
    | .trio => .atom ()
    | .pick => .atom ()
    | .join => .pair (.atom ()) (.atom ())
  first
    | .both => [(), ()]
    | .trio => [(), (), ()]
    | .pick => [(), ()]
    | .join => [()]
  others
    | .pick => [[()]]
    | _ => []

private abbrev tok : Ty Unit := .base ()
private abbrev pairTy : Ty Unit := .product tok tok
private abbrev tripleTy : Ty Unit := .product tok pairTy
private abbrev sumTy : Ty Unit := .coprod pairTy tok
private abbrev older : BoundCtx (Ty Unit) 2 := (BoundCtx.snoc .nil tok).snoc tok
private abbrev Term (n : Nat) := LetCase.LocallyNameless.Tm Empty Op n

private theorem separable : Separable older := separable_atoms (.snoc (.snoc .nil ()) ())

private abbrev exits : List (Ty Unit) := [pairTy, tok]
private abbrev pairExit : ExitAt exits pairTy := .here

private abbrev earlier : Slot older tok := ⟨1, rfl⟩

/-! ## The chain

Ask `both` on the earlier capture and bind the pair. Hold it. Ask `pick` on
the later capture and case on its reply. In the first arm, unpack the pair
payload into `x₁` and `x₂`, ask `join` on a chosen atom and the earlier
capture, with reply `c`, then destructure the held pair into `a` and `b`
and return a chosen pair. In the second arm, with payload `y`, destructure
the held pair and return a chosen pair. The held pair is destructured in
each arm separately. -/

/-- Under the held pair: the pair and the two captures. -/
private abbrev underPair : BoundCtx (Ty Unit) 3 := older.snoc pairTy
private abbrev laterUnder : Slot underPair tok := ⟨1, rfl⟩

/-- In the first arm, after the payload is unpacked: `x₂`, `x₁`, the
payload, the reply, the held pair and the two captures. -/
private abbrev firstArm : BoundCtx (Ty Unit) 7 :=
  (((underPair.snoc sumTy).snoc pairTy).snoc tok).snoc tok
private abbrev freshSecond : Slot firstArm tok := ⟨0, rfl⟩
private abbrev freshFirst : Slot firstArm tok := ⟨1, rfl⟩
private abbrev earlierFirstArm : Slot firstArm tok := ⟨6, rfl⟩

/-- The leaf of the first arm: `b`, `a`, `c`, `x₂`, `x₁`, the payload, the
reply, the held pair and the two captures. -/
private abbrev firstLeaf : BoundCtx (Ty Unit) 10 := ((firstArm.snoc tok).snoc tok).snoc tok
private abbrev leftB : Slot firstLeaf tok := ⟨0, rfl⟩
private abbrev leftA : Slot firstLeaf tok := ⟨1, rfl⟩
private abbrev leftC : Slot firstLeaf tok := ⟨2, rfl⟩

/-- The leaf of the second arm: `b`, `a`, `y`, the reply, the held pair
and the two captures. -/
private abbrev secondLeaf : BoundCtx (Ty Unit) 7 :=
  (((underPair.snoc sumTy).snoc tok).snoc tok).snoc tok
private abbrev rightB : Slot secondLeaf tok := ⟨0, rfl⟩
private abbrev rightA : Slot secondLeaf tok := ⟨1, rfl⟩
private abbrev rightY : Slot secondLeaf tok := ⟨2, rfl⟩
private abbrev rightEarlier : Slot secondLeaf tok := ⟨6, rfl⟩

/-- The tree with a chosen first argument of `join` and chosen returned
pairs in the two arms. -/
private def chainWith (joined : Slot firstArm tok) (fl sl : Slot firstLeaf tok)
    (fr sr : Slot secondLeaf tok) :
    Spelled older exits
      (.let₁ (.op Op.both (.bv 1))
        (.let₁ (.op Op.pick (.bv 1))
          (.case (.bv 0)
            (.let₂ (.bv 0)
              (.let₁ (.op Op.join (.pair (.bv joined.1) (.bv 6)))
                (.let₂ (.bv 5) (.inl (.pair (.bv fl.1) (.bv sl.1))))))
            (.let₂ (.bv 2) (.inl (.pair (.bv fr.1) (.bv sr.1)))))) : Term 2) :=
  .ask Op.both (.atom earlier)
    (.bind (.only [(), ()]
      (.hold [(), ()]
        (.ask Op.pick
          (.atom laterUnder)
          (.split [(), ()] [()] []
            (.step
              (.atom
                (.ask Op.join
                  (.pair (.atom joined) (.atom earlierFirstArm))
                  (.bind [()]
                    (.atom (.step (.atom (.done (.ret pairExit (.pair (.atom fl) (.atom sl)))))))))))
            (.bind [()] (.atom (.step (.atom (.done (.ret pairExit (.pair (.atom fr) (.atom sr)))))))))))))

/-- The normal form with a chosen first argument of `join` and chosen
returned pairs. The held pair is destructured once, before `pick`. The case
on the reply of `pick` directly follows `pick`. -/
private abbrev normalWith (joined : Fin 9) (fl sl : Fin 10) (fr sr : Fin 7) : Term 2 :=
  .let₁ (.op Op.both (.bv 1))
    (.let₂ (.bv 0)
      (.let₁ (.op Op.pick (.bv 3))
        (.case (.bv 0)
          (.let₂ (.bv 0)
            (.let₁ (.op Op.join (.pair (.bv joined) (.bv 8)))
              (.inl (.pair (.bv fl) (.bv sl)))))
          (.inl (.pair (.bv fr) (.bv sr))))))

/-- In the first arm `join` takes the first atom of the payload and the
earlier capture, and the first component of the held pair is returned with
the reply of `join`. In the second arm the second component of the held
pair is returned with the payload. -/
private abbrev chain := chainWith freshFirst leftA leftC rightB rightY

/-- The spelled term. -/
example : Spelled older exits
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.pick (.bv 1))
        (.case (.bv 0)
          (.let₂ (.bv 0)
            (.let₁ (.op Op.join (.pair (.bv 1) (.bv 6)))
              (.let₂ (.bv 5) (.inl (.pair (.bv 1) (.bv 2))))))
          (.let₂ (.bv 2) (.inl (.pair (.bv 0) (.bv 2)))))) : Term 2) := chain

/-- Its normal form. The three requests each occur once, in the same
order, and the case is on the reply of `pick` at the same point. -/
private theorem chain_normal : (chain.normal (.id older)).1 = normalWith 1 6 0 2 0 := rfl

/-- The native equation between the spelling and its normal form. -/
example : Equiv false Γ₀ older
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.pick (.bv 1))
        (.case (.bv 0)
          (.let₂ (.bv 0)
            (.let₁ (.op Op.join (.pair (.bv 1) (.bv 6)))
              (.let₂ (.bv 5) (.inl (.pair (.bv 1) (.bv 2))))))
          (.let₂ (.bv 2) (.inl (.pair (.bv 0) (.bv 2)))))) : Term 2)
    (.let₁ (.op Op.both (.bv 1))
      (.let₂ (.bv 0)
        (.let₁ (.op Op.pick (.bv 3))
          (.case (.bv 0)
            (.let₂ (.bv 0)
              (.let₁ (.op Op.join (.pair (.bv 1) (.bv 8)))
                (.inl (.pair (.bv 6) (.bv 0)))))
            (.inl (.pair (.bv 2) (.bv 0)))))))
    (packedExitType exits) :=
  spelled_equiv_normal chain

/-- In a larger context the normal form is the renamed normal form. -/
example : (chain.normal (BoundCtx.Renaming.succ older tok)).1 =
    (normalWith 1 6 0 2 0).rename Fin.succ :=
  spelled_normal_rename_term chain (.id older) (BoundCtx.Renaming.succ older tok)

/-! ## Variants -/

/-- `join` takes the second atom of the payload. -/
private abbrev otherFresh := chainWith freshSecond leftA leftC rightB rightY

/-- The first arm returns the other component of the held pair. -/
private abbrev otherHeldFirst := chainWith freshFirst leftB leftC rightB rightY

/-- The second arm returns the other component of the held pair. -/
private abbrev otherHeldSecond := chainWith freshFirst leftA leftC rightA rightY

/-- The second arm returns the earlier capture in place of its payload. -/
private abbrev captureSecond := chainWith freshFirst leftA leftC rightB rightEarlier

/-- The first arm returns its two atoms in the other order. -/
private abbrev otherOrder := chainWith freshFirst leftC leftA rightB rightY

example : (otherFresh.normal (.id older)).1 = normalWith 0 6 0 2 0 := rfl
example : (otherHeldFirst.normal (.id older)).1 = normalWith 1 5 0 2 0 := rfl
example : (otherHeldSecond.normal (.id older)).1 = normalWith 1 6 0 3 0 := rfl
example : (captureSecond.normal (.id older)).1 = normalWith 1 6 0 2 6 := rfl
example : (otherOrder.normal (.id older)).1 = normalWith 1 0 6 2 0 := rfl

/-- The contexts of the eager spelling. -/
private abbrev opened : BoundCtx (Ty Unit) 5 := ((older.snoc pairTy).snoc tok).snoc tok
private abbrev openedReply : BoundCtx (Ty Unit) 6 := opened.snoc sumTy
private abbrev openedFirst : BoundCtx (Ty Unit) 9 := ((openedReply.snoc pairTy).snoc tok).snoc tok
private abbrev openedFirstLeaf : BoundCtx (Ty Unit) 10 := openedFirst.snoc tok
private abbrev openedSecondLeaf : BoundCtx (Ty Unit) 7 := openedReply.snoc tok

private def eagerFirstLeaf :=
  Spelled.ret (Φ := Op) (β := openedFirstLeaf) pairExit (.pair (.atom ⟨6, rfl⟩) (.atom ⟨0, rfl⟩))

private def eagerJoin :=
  Spelled.ask Op.join (.pair (.atom (β := openedFirst) ⟨1, rfl⟩) (.atom ⟨8, rfl⟩))
    (.bind (.only [()] (.atom () eagerFirstLeaf)))

private def eagerSecondLeaf :=
  Spelled.ret (Φ := Op) (β := openedSecondLeaf) pairExit (.pair (.atom ⟨2, rfl⟩) (.atom ⟨0, rfl⟩))

private def eagerPick :=
  Spelled.ask Op.pick (.atom (β := opened) ⟨3, rfl⟩)
    (.bind (.split [(), ()] [()] []
      (.pair () () [] (.atom () eagerJoin))
      (.only [()] (.atom () eagerSecondLeaf))))

/-- The eager spelling: destructure the held pair at once, then ask `pick`
and case on its reply. It is the normal form of the held chain. -/
private def eager : Spelled older exits (normalWith 1 6 0 2 0) :=
  .ask Op.both (.atom earlier) (.bind (.only [(), ()] (.pair () () [] (.atom () eagerPick))))

private theorem eager_normal : (eager.normal (.id older)).1 = normalWith 1 6 0 2 0 := rfl

/-! ## A held triple across the request with two tags

Ask `trio` on the earlier capture and hold its triple. Ask `pick` on the
later capture and case on its reply. Each arm unpacks the held triple
completely and returns its second atom, with the first atom of the payload
in the first arm and with the payload in the second. The length of the
held tuple is not special. -/

private abbrev underTriple : BoundCtx (Ty Unit) 3 := older.snoc tripleTy

private abbrev tripleFirstLeaf : BoundCtx (Ty Unit) 11 :=
  (((((((underTriple.snoc sumTy).snoc pairTy).snoc tok).snoc tok).snoc tok).snoc pairTy).snoc tok).snoc tok

private abbrev tripleSecondLeaf : BoundCtx (Ty Unit) 9 :=
  (((((underTriple.snoc sumTy).snoc tok).snoc tok).snoc pairTy).snoc tok).snoc tok

private def triple : Spelled older exits
    (.let₁ (.op Op.trio (.bv 1))
      (.let₁ (.op Op.pick (.bv 1))
        (.case (.bv 0)
          (.let₂ (.bv 0) (.let₂ (.bv 4) (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 5))))))
          (.let₂ (.bv 2) (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 4))))))) : Term 2) :=
  .ask Op.trio (.atom earlier)
    (.bind (.only [(), (), ()]
      (.hold [(), (), ()]
        (.ask Op.pick
          (.atom (β := underTriple) ⟨1, rfl⟩)
          (.split [(), ()] [()] []
            (.step
              (.atom
                (.step
                  (.step
                    (.atom
                      (.done
                        (.ret pairExit (.pair (.atom (β := tripleFirstLeaf) ⟨1, rfl⟩) (.atom ⟨5, rfl⟩)))))))))
            (.bind [()]
              (.atom
                (.step
                  (.step
                    (.atom
                      (.done
                        (.ret pairExit
                          (.pair (.atom (β := tripleSecondLeaf) ⟨1, rfl⟩) (.atom ⟨4, rfl⟩))))))))))))))

/-- The held triple is unpacked completely before `pick`. -/
example : (triple.normal (.id older)).1 =
    (.let₁ (.op Op.trio (.bv 1))
      (.let₂ (.bv 0)
        (.let₂ (.bv 0)
          (.let₁ (.op Op.pick (.bv 5))
            (.case (.bv 0)
              (.let₂ (.bv 0) (.inl (.pair (.bv 5) (.bv 1))))
              (.inl (.pair (.bv 3) (.bv 0))))))) : Term 2) := rfl

/-! ## Ranked validity and ordered-exit arrows -/

private abbrev sentence {t u : Term 2} (p : Spelled older exits t) (q : Spelled older exits u) :
    RankedEquation (atomSig Unit Op) :=
  sentenceOf (entryOf p.graph) (entryOf q.graph)

/-- The held chain and the eager spelling are one sentence. -/
private theorem chain_eager : RankedValid false (sentence chain eager) :=
  (rankedValid_spelledTree_iff separable chain eager).mpr (chain_normal.trans eager_normal.symm)

/-- They have the same ordered-exit arrow at the ordered trace model with
atoms. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) =
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf eager.graph) :=
  (denoteRanked_spelledTree_iff separable chain eager).mpr (chain_normal.trans eager_normal.symm)

/-- Which atom of the compound payload the following request takes. -/
private theorem fresh_apart : ¬ RankedValid false (sentence chain otherFresh) := fun valid => by
  have same : normalWith 1 6 0 2 0 = normalWith 0 6 0 2 0 :=
    (rankedValid_spelledTree_iff separable chain otherFresh).mp valid
  simp at same

/-- Which component of the held pair the first arm returns. -/
private theorem first_apart : ¬ RankedValid false (sentence chain otherHeldFirst) := fun valid => by
  have same : normalWith 1 6 0 2 0 = normalWith 1 5 0 2 0 :=
    (rankedValid_spelledTree_iff separable chain otherHeldFirst).mp valid
  simp at same

/-- Which component of the held pair the second arm returns. The two
trees differ only under the second tag. -/
private theorem second_apart : ¬ RankedValid false (sentence chain otherHeldSecond) := fun valid => by
  have same : normalWith 1 6 0 2 0 = normalWith 1 6 0 3 0 :=
    (rankedValid_spelledTree_iff separable chain otherHeldSecond).mp valid
  simp at same

/-- The payload of the second tag and an older capture. -/
example : ¬ RankedValid false (sentence chain captureSecond) := fun valid => by
  have same : normalWith 1 6 0 2 0 = normalWith 1 6 0 2 6 :=
    (rankedValid_spelledTree_iff separable chain captureSecond).mp valid
  simp at same

/-- The order of the returned atoms in the first arm. -/
example : ¬ RankedValid false (sentence chain otherOrder) := fun valid => by
  have same : normalWith 1 6 0 2 0 = normalWith 1 0 6 2 0 :=
    (rankedValid_spelledTree_iff separable chain otherOrder).mp valid
  simp at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms,
and the model rejects each sentence. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf otherHeldFirst.graph) :=
  fun same => by
    have terms : normalWith 1 6 0 2 0 = normalWith 1 5 0 2 0 :=
      (denoteRanked_spelledTree_iff separable chain otherHeldFirst).mp same
    simp at terms

example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf otherHeldSecond.graph) :=
  fun same => by
    have terms : normalWith 1 6 0 2 0 = normalWith 1 6 0 3 0 :=
      (denoteRanked_spelledTree_iff separable chain otherHeldSecond).mp same
    simp at terms

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain otherHeldFirst) := fun holds =>
  first_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf otherHeldFirst.graph) (spelled_graph chain) (spelled_graph otherHeldFirst)).mpr holds)

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain otherHeldSecond) := fun holds =>
  second_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf otherHeldSecond.graph) (spelled_graph chain) (spelled_graph otherHeldSecond)).mpr holds)

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain otherFresh) := fun holds =>
  fresh_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf otherFresh.graph) (spelled_graph chain) (spelled_graph otherFresh)).mpr holds)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
