module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation denoteRanked)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetSeq.StraightLine.Structural (Slot Assembly)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
open scoped LetSeq.StraightLine.Structural Tagged

/-! ## Two reply shapes

There is one atom. `choose` takes one atom. Its reply has three ordered
tags: one atom, nothing, or a pair of atoms. `fetch` takes a pair of
atoms. Its reply has two tags: a pair of atoms, or one atom. Two older
atoms are captured. The exits are a pair of atoms and one atom. -/

private inductive Op | choose | fetch

local instance : TaggedSignature Unit Op where
  argument
    | .choose => .atom ()
    | .fetch => .pair (.atom ()) (.atom ())
  first
    | .choose => [()]
    | .fetch => [(), ()]
  others
    | .choose => [[], [(), ()]]
    | .fetch => [[()]]

private abbrev tok : Ty Unit := .base ()
private abbrev pairTy : Ty Unit := .product tok tok
private abbrev older : BoundCtx (Ty Unit) 2 := (BoundCtx.snoc .nil tok).snoc tok
private abbrev Term (n : Nat) := LetCase.LocallyNameless.Tm Empty Op n

/-- The reply of `choose`: an atom, or nothing, or a pair. -/
private abbrev chosen : Ty Unit := .coprod tok (.coprod .unit pairTy)
private abbrev chosenRest : Ty Unit := .coprod .unit pairTy

/-- The reply of `fetch`: a pair, or an atom. -/
private abbrev fetched : Ty Unit := .coprod pairTy tok

example : instrTrg (τ := Ty Unit) Op.choose = chosen ∧ instrTrg (τ := Ty Unit) Op.fetch = fetched := ⟨rfl, rfl⟩
example : instrSrc (τ := Ty Unit) Op.fetch = pairTy := rfl

private theorem separable : Separable older := separable_atoms (.snoc (.snoc .nil ()) ())

private abbrev exits : List (Ty Unit) := [pairTy, tok]
private abbrev pairExit : ExitAt exits pairTy := .here
private abbrev atomExit : ExitAt exits tok := .there .here

/-! ## The forced shape of each request

After `choose`: case on the reply. The first arm has the atom. Otherwise
case on the rest: the second arm has the unit, and the third arm unpacks
the pair into two atom slots. After `fetch`: the first arm unpacks the
pair and the second arm has the atom. -/

private def choose {n : Nat} {β : BoundCtx (Ty Unit) n} {L : List (Ty Unit)} (argument : Slot β tok)
    {one : Term (n + 2)} {none : Term (n + 3)} {two : Term (n + 5)}
    (atom : CaseTree .body ((β.snoc chosen).snoc tok) L one)
    (nothing : CaseTree .body (((β.snoc chosen).snoc chosenRest).snoc .unit) L none)
    (pair : CaseTree .body (((((β.snoc chosen).snoc chosenRest).snoc pairTy).snoc tok).snoc tok) L two) :
    CaseTree .body β L
      (.let₁ (.op Op.choose (.bv argument.1)) (.case (.bv 0) one (.case (.bv 0) none (.let₂ (.bv 0) two)))) :=
  .ask Op.choose (.atom argument)
    (.split [()] [] [[(), ()]] (.atom () atom)
      (.split [] [(), ()] [] (.unit nothing) (.only [(), ()] (.pair () () [] (.atom () pair)))))

private def fetch {n : Nat} {β : BoundCtx (Ty Unit) n} {L : List (Ty Unit)} (left right : Slot β tok)
    {two : Term (n + 4)} {one : Term (n + 2)}
    (pair : CaseTree .body ((((β.snoc fetched).snoc pairTy).snoc tok).snoc tok) L two)
    (atom : CaseTree .body ((β.snoc fetched).snoc tok) L one) :
    CaseTree .body β L
      (.let₁ (.op Op.fetch (.pair (.bv left.1) (.bv right.1))) (.case (.bv 0) (.let₂ (.bv 0) two) one)) :=
  .ask Op.fetch (.pair (.atom left) (.atom right))
    (.split [(), ()] [()] [] (.pair () () [] (.atom () pair)) (.only [()] (.atom () atom)))

private abbrev earlier : Slot older tok := ⟨1, rfl⟩
private abbrev later : Slot older tok := ⟨0, rfl⟩

/-- The contexts of the three arms of `choose`. The first has the reply
atom. The second has the unit. The third has the two reply atoms. Each
keeps the bound replies and everything above. -/
private abbrev atomArm {n : Nat} (β : BoundCtx (Ty Unit) n) : BoundCtx (Ty Unit) (n + 2) :=
  (β.snoc chosen).snoc tok
private abbrev unitArm {n : Nat} (β : BoundCtx (Ty Unit) n) : BoundCtx (Ty Unit) (n + 3) :=
  ((β.snoc chosen).snoc chosenRest).snoc .unit
private abbrev pairArm {n : Nat} (β : BoundCtx (Ty Unit) n) : BoundCtx (Ty Unit) (n + 5) :=
  ((((β.snoc chosen).snoc chosenRest).snoc pairTy).snoc tok).snoc tok

/-- The contexts of the two arms of `fetch`. -/
private abbrev fetchedPair {n : Nat} (β : BoundCtx (Ty Unit) n) : BoundCtx (Ty Unit) (n + 4) :=
  (((β.snoc fetched).snoc pairTy).snoc tok).snoc tok
private abbrev fetchedAtom {n : Nat} (β : BoundCtx (Ty Unit) n) : BoundCtx (Ty Unit) (n + 2) :=
  (β.snoc fetched).snoc tok

/-! ## A three-tag choice

Ask `choose` on the earlier capture. Under the first tag return the reply
atom. Under the second return the later capture. Under the third return
the two reply atoms as a pair. -/

private def three : CaseTree .body older exits
    (.let₁ (.op Op.choose (.bv 1))
      (.case (.bv 0) (.inr (.inl (.bv 0)))
        (.case (.bv 0) (.inr (.inl (.bv 3))) (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 0)))))) : Term 2) :=
  choose earlier (.ret (β := atomArm older) atomExit (.atom ⟨0, rfl⟩))
    (.ret (β := unitArm older) atomExit (.atom ⟨3, rfl⟩))
    (.ret (β := pairArm older) pairExit (.pair (.atom ⟨1, rfl⟩) (.atom ⟨0, rfl⟩)))

/-- The same tree returning the earlier capture under the second tag. -/
private def threeSecond :=
  choose (L := exits) earlier (.ret (β := atomArm older) atomExit (.atom ⟨0, rfl⟩))
    (.ret (β := unitArm older) atomExit (.atom ⟨4, rfl⟩))
    (.ret (β := pairArm older) pairExit (.pair (.atom ⟨1, rfl⟩) (.atom ⟨0, rfl⟩)))

/-- The same tree returning the two reply atoms in the other order under
the third tag. -/
private def threeThird :=
  choose (L := exits) earlier (.ret (β := atomArm older) atomExit (.atom ⟨0, rfl⟩))
    (.ret (β := unitArm older) atomExit (.atom ⟨3, rfl⟩))
    (.ret (β := pairArm older) pairExit (.pair (.atom ⟨0, rfl⟩) (.atom ⟨1, rfl⟩)))

/-- Return the earlier capture under the first tag and the later capture
under the second. -/
private def tagsOne :=
  choose (L := exits) earlier (.ret (β := atomArm older) atomExit (.atom ⟨3, rfl⟩))
    (.ret (β := unitArm older) atomExit (.atom ⟨3, rfl⟩))
    (.ret (β := pairArm older) pairExit (.pair (.atom ⟨1, rfl⟩) (.atom ⟨0, rfl⟩)))

/-- Return the later capture under the first tag and the earlier capture
under the second. -/
private def tagsOther :=
  choose (L := exits) earlier (.ret (β := atomArm older) atomExit (.atom ⟨2, rfl⟩))
    (.ret (β := unitArm older) atomExit (.atom ⟨4, rfl⟩))
    (.ret (β := pairArm older) pairExit (.pair (.atom ⟨1, rfl⟩) (.atom ⟨0, rfl⟩)))

/-! ## A pair reply used with an older capture in a nested request

Ask `fetch` on the two captures. Under the pair tag, with reply atoms `x`
and `y`, ask `fetch` again on `y` and the earlier capture. Under its pair
tag, with reply atoms `p` and `q`, return the pair of `p` and `x`. Under
its atom tag return that atom. Under the outer atom tag ask `choose` on
the reply atom. -/

/-- After the outer pair tag: `y`, `x`, the pair, the reply, the captures. -/
private abbrev pairCtx : BoundCtx (Ty Unit) 6 := fetchedPair older
private abbrev replyY : Slot pairCtx tok := ⟨0, rfl⟩
private abbrev replyX : Slot pairCtx tok := ⟨1, rfl⟩
private abbrev earlierIn : Slot pairCtx tok := ⟨5, rfl⟩

/-- After the inner pair tag: `q`, `p`, and everything above. -/
private abbrev innerCtx : BoundCtx (Ty Unit) 10 := fetchedPair pairCtx
private abbrev replyQ : Slot innerCtx tok := ⟨0, rfl⟩
private abbrev replyP : Slot innerCtx tok := ⟨1, rfl⟩
private abbrev outerX : Slot innerCtx tok := ⟨5, rfl⟩

/-- After the outer atom tag: the reply atom, the reply, the captures. -/
private abbrev atomCtx : BoundCtx (Ty Unit) 4 := fetchedAtom older
private abbrev replyW : Slot atomCtx tok := ⟨0, rfl⟩

private def afterAtom :=
  choose (L := exits) replyW (.ret (β := atomArm atomCtx) atomExit (.atom ⟨0, rfl⟩))
    (.ret (β := unitArm atomCtx) atomExit (.atom ⟨6, rfl⟩))
    (.ret (β := pairArm atomCtx) pairExit (.pair (.atom ⟨1, rfl⟩) (.atom ⟨0, rfl⟩)))

private def nested :=
  fetch (L := exits) earlier later
    (fetch replyY earlierIn (.ret pairExit (.pair (.atom replyP) (.atom outerX)))
      (.ret (β := fetchedAtom pairCtx) atomExit (.atom ⟨0, rfl⟩)))
    afterAtom

/-- The nested request takes the other component of the outer pair. -/
private def nestedArgument :=
  fetch (L := exits) earlier later
    (fetch replyX earlierIn (.ret pairExit (.pair (.atom replyP) (.atom outerX)))
      (.ret (β := fetchedAtom pairCtx) atomExit (.atom ⟨0, rfl⟩)))
    afterAtom

/-- The returned pair takes the other component of the inner pair. -/
private def nestedComponent :=
  fetch (L := exits) earlier later
    (fetch replyY earlierIn (.ret pairExit (.pair (.atom replyQ) (.atom outerX)))
      (.ret (β := fetchedAtom pairCtx) atomExit (.atom ⟨0, rfl⟩)))
    afterAtom

/-- The nested request has its two arguments exchanged. -/
private def nestedOrder :=
  fetch (L := exits) earlier later
    (fetch earlierIn replyY (.ret pairExit (.pair (.atom replyP) (.atom outerX)))
      (.ret (β := fetchedAtom pairCtx) atomExit (.atom ⟨0, rfl⟩)))
    afterAtom

/-! ## Sentences between the graphs read back from the trees -/

private abbrev sentence {t u : Term 2} (p : CaseTree .body older exits t) (q : CaseTree .body older exits u) :
    RankedEquation (atomSig Unit Op) :=
  sentenceOf (entryOf p.graph) (entryOf q.graph)

example : (sentence three threeSecond).1.exits = [pairTy, tok] := rfl

/-! ## The tag of a three-tag reply is observed -/

/-- What is returned under the second tag. -/
private theorem second_apart : ¬ RankedValid false (sentence three threeSecond) := fun valid => by
  have same := (rankedValid_caseTree_iff separable three threeSecond).mp valid
  simp [ExitAt.term, argTerm] at same

/-- The assignment of two behaviours to the first two tags. -/
example : ¬ RankedValid false (sentence tagsOne tagsOther) := fun valid => by
  have same := (rankedValid_caseTree_iff separable tagsOne tagsOther).mp valid
  simp [ExitAt.term, argTerm] at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms,
and the model rejects the sentence. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf three.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf threeSecond.graph) :=
  fun same => by
    have terms := (denoteRanked_caseTree_iff separable three threeSecond).mp same
    simp [ExitAt.term, argTerm] at terms

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence three threeSecond) := fun holds =>
  second_apart ((rankedValid_branching_iff_atomTrace separable (entryOf three.graph)
    (entryOf threeSecond.graph) (branching_graph three) (branching_graph threeSecond)).mpr holds)

/-! ## The components of a pair reply are observed -/

/-- The order of the two reply atoms under the third tag. -/
example : ¬ RankedValid false (sentence three threeThird) := fun valid => by
  have same := (rankedValid_caseTree_iff separable three threeThird).mp valid
  simp [ExitAt.term, argTerm] at same

/-- Which component of the outer pair the nested request takes, beside
the older capture. -/
example : ¬ RankedValid false (sentence nested nestedArgument) := fun valid => by
  have same := (rankedValid_caseTree_iff separable nested nestedArgument).mp valid
  simp at same

/-- The order of the reply component and the older capture in the nested
request. -/
example : ¬ RankedValid false (sentence nested nestedOrder) := fun valid => by
  have same := (rankedValid_caseTree_iff separable nested nestedOrder).mp valid
  simp at same

/-- Which component of the inner pair is returned with the outer one. -/
example : ¬ RankedValid false (sentence nested nestedComponent) := fun valid => by
  have same := (rankedValid_caseTree_iff separable nested nestedComponent).mp valid
  simp [ExitAt.term, argTerm] at same

/-! ## A valid sentence

The second graph is read back from the operand emitted by the first. -/

private def nestedAgain : CheckedTable Op older exits :=
  CheckedTable.ofLetCase (List.cons_ne_nil _ _) nested.graph.toLetCase.2

private theorem again_branching : Branching (emitted (P := atomSig Unit Op) (entryOf nestedAgain)) :=
  Branching.congr (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) nested.graph.toLetCase.2)
    (branching_graph nested)

private theorem again_valid : RankedValid false (sentenceOf (entryOf nested.graph) (entryOf nestedAgain)) :=
  (rankedValid_branching_iff separable (entryOf nested.graph) (entryOf nestedAgain) (branching_graph nested)
    again_branching).mpr (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) nested.graph.toLetCase.2).symm

/-- The two graphs have the same ordered-exit arrow at the ordered trace
model with atoms. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf nested.graph) =
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf nestedAgain) :=
  (rankedValid_branching_iff_atomTrace separable (entryOf nested.graph) (entryOf nestedAgain)
    (branching_graph nested) again_branching).mp again_valid

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
