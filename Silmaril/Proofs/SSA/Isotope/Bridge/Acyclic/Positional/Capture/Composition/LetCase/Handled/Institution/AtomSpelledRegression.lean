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

/-! ## Three reply shapes

There is one atom. `both` takes one atom and replies with a pair of atoms
under its one tag. `fetch` takes a pair of atoms and replies with a pair of
atoms or with one atom. `choose` takes one atom and replies with one atom,
nothing, or a pair of atoms. Two older atoms are captured. The exits are a
pair of atoms and one atom. -/

private inductive Op | both | fetch | choose

local instance : TaggedSignature Unit Op where
  argument
    | .both => .atom ()
    | .fetch => .pair (.atom ()) (.atom ())
    | .choose => .atom ()
  first
    | .both => [(), ()]
    | .fetch => [(), ()]
    | .choose => [()]
  others
    | .both => []
    | .fetch => [[()]]
    | .choose => [[], [(), ()]]

private abbrev tok : Ty Unit := .base ()
private abbrev pairTy : Ty Unit := .product tok tok
private abbrev older : BoundCtx (Ty Unit) 2 := (BoundCtx.snoc .nil tok).snoc tok
private abbrev Term (n : Nat) := LetCase.LocallyNameless.Tm Empty Op n

example : instrTrg (τ := Ty Unit) Op.both = pairTy := rfl
example : instrTrg (τ := Ty Unit) Op.fetch = .coprod pairTy tok := rfl
example : instrTrg (τ := Ty Unit) Op.choose = .coprod tok (.coprod .unit pairTy) := rfl

private theorem separable : Separable older := separable_atoms (.snoc (.snoc .nil ()) ())

private abbrev exits : List (Ty Unit) := [pairTy, tok]
private abbrev pairExit : ExitAt exits pairTy := .here
private abbrev atomExit : ExitAt exits tok := .there .here

private abbrev earlier : Slot older tok := ⟨1, rfl⟩

/-! ## A pair request destructured at once, then a case request with a pair arm

Ask `both` on the earlier capture and destructure the reply at the
request: `x` and `y` are slots and no slot holds the pair. Then ask `fetch`
on `y` and the earlier capture, and case on that request. Under the pair
tag the payload is destructured into `p` and `q`, and the pair of `p` and
the earlier capture is returned. Under the atom tag the atom is returned. -/

/-- After the pair request: `y`, `x` and the two captures. -/
private abbrev afterBoth : BoundCtx (Ty Unit) 4 := (older.snoc tok).snoc tok
private abbrev replyY : Slot afterBoth tok := ⟨0, rfl⟩
private abbrev replyX : Slot afterBoth tok := ⟨1, rfl⟩
private abbrev earlierIn : Slot afterBoth tok := ⟨3, rfl⟩

/-- Under the pair tag of `fetch`: `q`, `p`, the payload, and everything above. -/
private abbrev pairArm : BoundCtx (Ty Unit) 7 := ((afterBoth.snoc pairTy).snoc tok).snoc tok
private abbrev replyQ : Slot pairArm tok := ⟨0, rfl⟩
private abbrev replyP : Slot pairArm tok := ⟨1, rfl⟩
private abbrev outerX : Slot pairArm tok := ⟨4, rfl⟩
private abbrev earlierDeep : Slot pairArm tok := ⟨6, rfl⟩

/-- Under the atom tag of `fetch`: the atom and everything above. -/
private abbrev atomArm : BoundCtx (Ty Unit) 5 := afterBoth.snoc tok
private abbrev replyR : Slot atomArm tok := ⟨0, rfl⟩

/-- The tree with a chosen `fetch` argument and a chosen returned pair. -/
private def spelledWith (left right : Slot afterBoth tok) (first second : Slot pairArm tok) :
    Spelled older exits
      (.let₂ (.op Op.both (.bv 1))
        (.case (.op Op.fetch (.pair (.bv left.1) (.bv right.1)))
          (.let₂ (.bv 0) (.inl (.pair (.bv first.1) (.bv second.1))))
          (.inr (.inl (.bv 0)))) : Term 2) :=
  .ask Op.both (.atom earlier)
    (.destruct () () []
      (.atom ()
        (.ask Op.fetch (.pair (.atom left) (.atom right))
          (.branch [(), ()] [()] []
            (.pair () () [] (.atom () (.ret pairExit (.pair (.atom first) (.atom second)))))
            (.only [()] (.atom () (.ret atomExit (.atom replyR))))))))

private abbrev nested := spelledWith replyY earlierIn replyP earlierDeep

/-- The spelled term. Both requests are consumed where they are asked. -/
example : Spelled older exits
    (.let₂ (.op Op.both (.bv 1))
      (.case (.op Op.fetch (.pair (.bv 0) (.bv 3)))
        (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 6))))
        (.inr (.inl (.bv 0)))) : Term 2) := nested

/-- The normal form with a chosen `fetch` argument and a chosen returned
pair. It binds each reply first. -/
private abbrev normalWith (left right : Fin 5) (first second : Fin 9) : Term 2 :=
  .let₁ (.op Op.both (.bv 1))
    (.let₂ (.bv 0)
      (.let₁ (.op Op.fetch (.pair (.bv left) (.bv right)))
        (.case (.bv 0)
          (.let₂ (.bv 0) (.inl (.pair (.bv first) (.bv second))))
          (.inr (.inl (.bv 0))))))

/-- The normal form of the tree. The requests are in the same order with
the same arguments, the exits are the same, and the fresh atom and the
older capture are the same slots, counted past the two reply slots. -/
private abbrev nestedNormal : Term 2 := normalWith 0 4 1 8

example : (nested.normal (.id older)).1 = nestedNormal := rfl

/-- The native equation between the two spellings. -/
example : Equiv false Γ₀ older
    (.let₂ (.op Op.both (.bv 1))
      (.case (.op Op.fetch (.pair (.bv 0) (.bv 3)))
        (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 6))))
        (.inr (.inl (.bv 0)))) : Term 2)
    nestedNormal (packedExitType exits) :=
  spelled_equiv_normal nested

/-- The law at the first request alone: the pair is bound and then
destructured, and the body is weakened past the bound pair. -/
example : Equiv false Γ₀ older
    (.let₂ (.op Op.both (.bv 1))
      (.case (.op Op.fetch (.pair (.bv 0) (.bv 3)))
        (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 6))))
        (.inr (.inl (.bv 0)))) : Term 2)
    (.let₁ (.op Op.both (.bv 1))
      (.let₂ (.bv 0)
        (.case (.op Op.fetch (.pair (.bv 0) (.bv 4)))
          (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 7))))
          (.inr (.inl (.bv 0))))))
    (packedExitType exits) :=
  ask_pair_bind Op.both (.atom earlier) rfl
    (Spelled.ask Op.fetch (.pair (.atom replyY) (.atom earlierIn))
      (.branch [(), ()] [()] []
        (.pair () () [] (.atom () (.ret pairExit (.pair (.atom replyP) (.atom earlierDeep)))))
        (.only [()] (.atom () (.ret atomExit (.atom replyR)))))).typing.toHasType

/-! ## Variants in the same spelling -/

/-- The other component of the inner pair is returned. -/
private abbrev otherComponent := spelledWith replyY earlierIn replyQ earlierDeep

/-- The fresh atom `x` is returned in place of the older capture. -/
private abbrev freshForOlder := spelledWith replyY earlierIn replyP outerX

/-- The nested request takes `x` in place of `y`. -/
private abbrev otherArgument := spelledWith replyX earlierIn replyP earlierDeep

/-- The nested request has its two arguments exchanged. -/
private abbrev otherOrder := spelledWith earlierIn replyY replyP earlierDeep

example : (otherComponent.normal (.id older)).1 = normalWith 0 4 0 8 := rfl
example : (freshForOlder.normal (.id older)).1 = normalWith 0 4 1 5 := rfl
example : (otherArgument.normal (.id older)).1 = normalWith 1 4 1 8 := rfl
example : (otherOrder.normal (.id older)).1 = normalWith 4 0 1 8 := rfl

/-! ## Completeness applied to the spelled syntax -/

private abbrev sentence {t u : Term 2} (p : Spelled older exits t) (q : Spelled older exits u) :
    RankedEquation (atomSig Unit Op) :=
  sentenceOf (entryOf p.graph) (entryOf q.graph)

example : (sentence nested otherComponent).1.exits = [pairTy, tok] := rfl

/-- Which component of the destructured pair arm is returned. -/
private theorem component_apart : ¬ RankedValid false (sentence nested otherComponent) := fun valid => by
  have same : normalWith 0 4 1 8 = normalWith 0 4 0 8 :=
    (rankedValid_spelledTree_iff separable nested otherComponent).mp valid
  simp at same

/-- A fresh atom and the older capture in the returned pair. -/
example : ¬ RankedValid false (sentence nested freshForOlder) := fun valid => by
  have same : normalWith 0 4 1 8 = normalWith 0 4 1 5 :=
    (rankedValid_spelledTree_iff separable nested freshForOlder).mp valid
  simp at same

/-- Which component of the destructured request the nested request takes. -/
example : ¬ RankedValid false (sentence nested otherArgument) := fun valid => by
  have same : normalWith 0 4 1 8 = normalWith 1 4 1 8 :=
    (rankedValid_spelledTree_iff separable nested otherArgument).mp valid
  simp at same

/-- The order of the fresh atom and the older capture in the nested request. -/
example : ¬ RankedValid false (sentence nested otherOrder) := fun valid => by
  have same : normalWith 0 4 1 8 = normalWith 4 0 1 8 :=
    (rankedValid_spelledTree_iff separable nested otherOrder).mp valid
  simp at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms,
and the model rejects the sentence. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf nested.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf otherComponent.graph) :=
  fun same => by
    have terms : normalWith 0 4 1 8 = normalWith 0 4 0 8 :=
      (denoteRanked_spelledTree_iff separable nested otherComponent).mp same
    simp at terms

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence nested otherComponent) := fun holds =>
  component_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf nested.graph)
    (entryOf otherComponent.graph) (spelled_graph nested) (spelled_graph otherComponent)).mpr holds)

/-! ## The spelling and its normal form are one sentence -/

private theorem spellings_valid :
    RankedValid false (sentenceOf (entryOf nested.graph) (entryOf (nested.normal (.id older)).2.graph)) :=
  rankedValid_spelled_normal separable nested

example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf nested.graph) =
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op)
      (entryOf (nested.normal (.id older)).2.graph) :=
  (rankedValid_branching_iff_atomTrace separable (entryOf nested.graph)
    (entryOf (nested.normal (.id older)).2.graph) (branching_of_spelled (spelled_graph nested))
    (branching_graph (nested.normal (.id older)).2)).mp spellings_valid

/-! ## A three-tag request cased on at once

Ask `choose` on the earlier capture and case on the request. The first arm
has the atom. The rest of the reply is a bound slot and is cased on: the
second arm has nothing and returns the later capture, and the third arm
destructures its pair and returns it. -/

private abbrev atomTag : BoundCtx (Ty Unit) 3 := older.snoc tok
private abbrev restTy : Ty Unit := .coprod .unit pairTy
private abbrev unitTag : BoundCtx (Ty Unit) 4 := (older.snoc restTy).snoc .unit
private abbrev pairTag : BoundCtx (Ty Unit) 6 := (((older.snoc restTy).snoc pairTy).snoc tok).snoc tok

private def three (under : Slot unitTag tok) : Spelled older exits
    (.case (.op Op.choose (.bv 1)) (.inr (.inl (.bv 0)))
      (.case (.bv 0) (.inr (.inl (.bv under.1))) (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 0))))) : Term 2) :=
  .ask Op.choose (.atom earlier)
    (.branch [()] [] [[(), ()]]
      (.atom () (.ret (β := atomTag) atomExit (.atom ⟨0, rfl⟩)))
      (.split [] [(), ()] []
        (.unit (.ret atomExit (.atom under)))
        (.only [(), ()]
          (.pair () () [] (.atom () (.ret (β := pairTag) pairExit (.pair (.atom ⟨1, rfl⟩) (.atom ⟨0, rfl⟩))))))))

/-- Its normal form binds the reply and cases on the bound slot twice. -/
example : ((three ⟨2, rfl⟩).normal (.id older)).1 =
    (.let₁ (.op Op.choose (.bv 1))
      (.case (.bv 0) (.inr (.inl (.bv 0)))
        (.case (.bv 0) (.inr (.inl (.bv 3))) (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 0)))))) : Term 2) := rfl

/-- What is returned under the second of the three tags is observed. -/
example : ¬ RankedValid false (sentence (three ⟨2, rfl⟩) (three ⟨3, rfl⟩)) := fun valid => by
  have same : (.let₁ (.op Op.choose (.bv 1))
      (.case (.bv 0) (.inr (.inl (.bv 0)))
        (.case (.bv 0) (.inr (.inl (.bv 3))) (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 0)))))) : Term 2) =
      .let₁ (.op Op.choose (.bv 1))
        (.case (.bv 0) (.inr (.inl (.bv 0)))
          (.case (.bv 0) (.inr (.inl (.bv 4))) (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 0)))))) :=
    (rankedValid_spelledTree_iff separable (three ⟨2, rfl⟩) (three ⟨3, rfl⟩)).mp valid
  simp at same

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
