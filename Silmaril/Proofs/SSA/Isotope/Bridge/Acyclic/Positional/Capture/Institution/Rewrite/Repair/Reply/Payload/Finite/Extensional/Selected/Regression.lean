module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Selected.Thms

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional.Selected

open CategoryTheory
open Kleisli (value)
open LambdaSSA.Region (packedExitType)
open LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement (ReadTree replyInput)

private abbrev tail : List Sorts := [Bit]
private def first : Position (Bit :: tail) := ⟨0, rfl⟩
private def second : Position (Bit :: tail) := ⟨1, rfl⟩

private def fixture (bound : Bool) (result : Expr 2) (target : Position (Bit :: tail)) :
    ReadTree (Bit :: tail) 0 :=
  .request [false] true bound
    (.request [] false bound (.retExpr [] first (.literal false))
      (.testRequest [false] 1 false bound bound
        (.retExpr [true] first result) (.ret [] first 0)
        (.retExpr [true] target result) (.ret [] second 0)))
    (.ret [] second 0)

private def before := fixture true (.read 1) second
private def table := fixture false (Expr.quote 2 (fun env => env 1)) second
private def differentExit := fixture true (.read 1) first

-- The outer bit still selects the third request. The terminal reads
-- the other retained bit directly or through an explicit native table.
private theorem sameArrow : denotation before = denotation table := by
  apply (denotation_eq_iff_normal Bit tail _ _).mpr
  have tableEntry : (Expr.quote 2 (fun env => env 1)).eval = (Expr.read (1 : Fin 2)).eval :=
    funext (Expr.quote_eval 2 (fun env => env 1))
  simp only [before, table, fixture, witnessed, Source.normal, ReadTree.witnessed,
    List.foldr_cons, List.foldr_nil, Tree.normal, tableEntry]

example : Derivable false (equation Bit tail before table) :=
  (denotation_eq_iff_derivable Bit tail _ _).mp sameArrow

-- Fix both prior replies and the last reply. Changing the outward
-- position alone separates the packed arrows for the same output type.
example : denotation before ≠ denotation differentExit := by
  intro same
  have normal := (denotation_eq_iff_normal Bit tail _ _).mp same
  have selected := (Path.emit.inj normal).2
  have outer := (Path.request.inj selected).2.2.1
  have inner := (Path.request.inj outer).2.2.2.2
  have guard := (Path.emit.inj inner).2
  have reply := (Path.request.inj guard).2.1
  have pos := (Path.ret.inj (Path.emit.inj reply).2).1
  have atSlot := congrArg (fun p : Position (Bit :: tail) => p.1.val) pos
  contradiction

private def openFixture (bound : Bool) (result : Expr 2) (target : Position (Bit :: tail)) :
    ReadTree (Bit :: tail) 2 :=
  .testRequest [] 1 false bound bound
    (.ret [true] first 1) (.ret [] first 0)
    (.retExpr [true] target result) (.ret [] second 0)

private def openRead := openFixture true (.read 1) second
private def openTable := openFixture false (Expr.quote 2 (fun env => env 1)) second
private def openWrongExit := openFixture true (.read 1) first

private theorem openNormal (env : Assignment 2) :
    (witnessed openRead).normal env = (witnessed openTable).normal env := by
  have tableEntry : (Expr.quote 2 (fun env => env 1)).eval = (Expr.read (1 : Fin 2)).eval :=
    funext (Expr.quote_eval 2 (fun env => env 1))
  simp only [openRead, openTable, openFixture, witnessed, Source.normal, ReadTree.witnessed,
    List.foldr_cons, List.foldr_nil, Tree.normal, tableEntry]

private theorem openDerived : Derivable false (equation Bit tail openRead openTable) :=
  Extensional.derive_normal Bit tail _ _ openNormal

example : denotation openRead = denotation openTable :=
  (denotation_eq_iff_derivable Bit tail _ _).mpr openDerived

private abbrev Packed := value (packedExitType (Bit :: tail))

private def assignment (older newer : Bool) : Assignment 2 :=
  (Assignment.push (n := 0) Fin.elim0 older).push newer

-- Evaluate one and the same arrow at the actual nested product input.
-- The older bit controls the request and exit, while the newer bit is returned.
set_option backward.isDefEq.respectTransparency false in
private theorem runOpen (older newer : Bool) :
    afterPayload older false false
      ((denotation openRead).of ((PUnit.unit, bit older), bit newer)).outcomes =
      {(.ok (if older then Sum.inr (Sum.inl (bit newer)) else Sum.inl (bit newer) : Packed),
        FreeMonoid.of (.emit true))} := by
  change afterPayload older false false
    ((denotation openRead).of (replyInput 2 (assignment older newer))).outcomes = _
  rw [denotation_outcomes_at_assignment Bit tail, witnessed, Extensional.tree_programOutcomes_eq]
  have selected := Normal.afterTestRequest (L := Bit :: tail) (1 : Fin 2) false
    (.emit true (.ret first (Expr.read 1).eval)) (.ret first (Expr.read 0).eval)
    (.emit true (.ret second (Expr.read 1).eval)) (.ret second (Expr.read 0).eval)
    (assignment older newer) false false
  cases older
  · refine selected.trans ?_
    change prepend (.emit true) '' {(.ok (Sum.inl (bit newer) : Packed), 1)} = _
    simp only [Set.image_singleton, prepend, mul_one]
    rfl
  · refine selected.trans ?_
    change prepend (.emit true) '' {(.ok (Sum.inr (Sum.inl (bit newer)) : Packed), 1)} = _
    simp only [Set.image_singleton, prepend, mul_one]
    rfl

example :
    afterPayload false false false
      ((denotation openRead).of ((PUnit.unit, bit false), bit true)).outcomes =
      {(.ok (Sum.inl (bit true) : Packed), FreeMonoid.of (.emit true))} :=
  runOpen false true

example :
    afterPayload true false false
      ((denotation openRead).of ((PUnit.unit, bit true), bit true)).outcomes =
      {(.ok (Sum.inr (Sum.inl (bit true)) : Packed), FreeMonoid.of (.emit true))} :=
  runOpen true true

example : ¬ Derivable false (equation Bit tail openRead openWrongExit) := by
  intro derivation
  have equal := (denotation_eq_iff_derivable Bit tail _ _).mpr derivation
  have normal := (denotation_eq_iff_pointwise_normal Bit tail _ _).mp equal (assignment true true)
  have pos := (Path.ret.inj (Path.emit.inj (Path.request.inj normal).2.1).2).1
  have atSlot := congrArg (fun p : Position (Bit :: tail) => p.1.val) pos
  contradiction

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional.Selected
