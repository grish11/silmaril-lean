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

/-! ## Two ordered exits of the same atom sort

There is one atom. The primitive takes one atom and replies with one atom
under the first or the second tag. Two older atoms are captured. Both exits
carry the one atom sort, so an exit is not determined by the sort of what
is returned. -/

private inductive Probe | probe

local instance : TaggedSignature Unit Probe := ⟨fun _ => .atom (), fun _ => [()], fun _ => [[()]]⟩

private abbrev tok : Ty Unit := .base ()
private abbrev replyTy : Ty Unit := .coprod tok tok
private abbrev older : BoundCtx (Ty Unit) 2 := (BoundCtx.snoc .nil tok).snoc tok
private abbrev Term (n : Nat) := LetCase.LocallyNameless.Tm Empty Probe n

private theorem separable : Separable older := separable_atoms (.snoc (.snoc .nil ()) ())

private abbrev exits : List (Ty Unit) := [tok, tok]
private abbrev first : ExitAt exits tok := .here
private abbrev second : ExitAt exits tok := .there .here

example : first.index = 0 ∧ second.index = 1 := ⟨rfl, rfl⟩

/-- The same token at the two exits gives two different values. -/
example (x y : Nat) : first.value x ≠ second.value y := fun same => by
  obtain ⟨-, -, position⟩ := ExitAt.value_inj first second x y same
  exact absurd position (by decide)

private abbrev earlier : Slot older tok := ⟨1, rfl⟩
private abbrev armCtx : BoundCtx (Ty Unit) 4 := (older.snoc replyTy).snoc tok
private abbrev payload : Slot armCtx tok := ⟨0, rfl⟩
private abbrev innerCtx : BoundCtx (Ty Unit) 6 := (armCtx.snoc replyTy).snoc tok
private abbrev fresh : Slot innerCtx tok := ⟨0, rfl⟩
private abbrev outer : Slot innerCtx tok := ⟨2, rfl⟩

/-- The forced case split and unpacking of a reply, from the two arms. -/
private def arms {n : Nat} {β : BoundCtx (Ty Unit) n} {L : List (Ty Unit)} {l r : Term (n + 2)}
    (first : CaseTree .body ((β.snoc replyTy).snoc tok) L l)
    (second : CaseTree .body ((β.snoc replyTy).snoc tok) L r) :
    CaseTree (.tags [[()], [()]]) (β.snoc replyTy) L (.case (.bv 0) l r) :=
  .split [()] [()] [] (.atom () first) (.only [()] (.atom () second))

/-- A request: bind the reply and continue with the two arms. -/
private def probe {n : Nat} {β : BoundCtx (Ty Unit) n} {L : List (Ty Unit)} (argument : Slot β tok)
    {l r : Term (n + 2)} (first : CaseTree .body ((β.snoc replyTy).snoc tok) L l)
    (second : CaseTree .body ((β.snoc replyTy).snoc tok) L r) :
    CaseTree .body β L (.let₁ (.op Probe.probe (.bv argument.1)) (.case (.bv 0) l r)) :=
  .ask Probe.probe (.atom argument) (arms first second)

/-! ## Case trees over the two exits -/

/-- Return the earlier capture at the first exit. -/
private def leaveFirst : CaseTree .body older exits (.inl (.bv 1) : Term 2) := .ret first (.atom earlier)

/-- Return the same capture at the second exit. -/
private def leaveSecond : CaseTree .body older exits (.inr (.inl (.bv 1)) : Term 2) :=
  .ret second (.atom earlier)

/-- Probe the earlier capture. Return the payload at the first exit under
the first tag and at the second exit under the second tag. -/
private def split : CaseTree .body older exits
    (.let₁ (.op Probe.probe (.bv 1)) (.case (.bv 0) (.inl (.bv 0)) (.inr (.inl (.bv 0)))) : Term 2) :=
  probe earlier (.ret first (.atom payload)) (.ret second (.atom payload))

/-- The same request and payloads, leaving by the second exit under both tags. -/
private def merged : CaseTree .body older exits
    (.let₁ (.op Probe.probe (.bv 1)) (.case (.bv 0) (.inr (.inl (.bv 0))) (.inr (.inl (.bv 0)))) : Term 2) :=
  probe earlier (.ret second (.atom payload)) (.ret second (.atom payload))

/-- Probe the earlier capture, then under the first tag probe the payload.
The inner first arm returns the fresh reply atom at the first exit. -/
private def deep :=
  probe (L := exits) earlier
    (probe payload (.ret first (.atom fresh)) (.ret second (.atom outer)))
    (.ret second (.atom payload))

/-- The same tree with the exit unchanged and the outer payload returned
in place of the fresh reply atom. -/
private def deepOuter :=
  probe (L := exits) earlier
    (probe payload (.ret first (.atom outer)) (.ret second (.atom outer)))
    (.ret second (.atom payload))

/-- The same tree with the fresh reply atom unchanged and returned at the
second exit. -/
private def deepSecond :=
  probe (L := exits) earlier
    (probe payload (.ret second (.atom fresh)) (.ret second (.atom outer)))
    (.ret second (.atom payload))

/-! ## The ranked sentences are at the two original exits -/

private abbrev sentence {t u : Term 2} (p : CaseTree .body older exits t) (q : CaseTree .body older exits u) :
    RankedEquation (atomSig Unit Probe) :=
  sentenceOf (entryOf p.graph) (entryOf q.graph)

example : (sentence leaveFirst leaveSecond).1.exits = [tok, tok] := rfl

/-- The region emitted from the read-back graph has the two ordered exits. -/
example : Region.HasType older.toList leaveSecond.graph.toSSA [tok, tok] := leaveSecond.graph.toSSA_hasType

/-! ## Exit choice is observed -/

/-- The same capture at a different exit. -/
private theorem exits_apart : ¬ RankedValid false (sentence leaveFirst leaveSecond) := fun valid => by
  have same := (rankedValid_caseTree_iff separable leaveFirst leaveSecond).mp valid
  simp at same

/-- The ordered-exit arrows of the two graphs differ at the ordered trace
model with atoms. These are the arrows of the ranked room into the two
exits. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Probe)) (atomTraceModel Unit Probe) (entryOf leaveFirst.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Probe)) (atomTraceModel Unit Probe) (entryOf leaveSecond.graph) :=
  fun same => by
    have terms := (denoteRanked_caseTree_iff separable leaveFirst leaveSecond).mp same
    simp at terms

/-- The model rejects the sentence. -/
example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Probe))
    (atomSig Unit Probe)).Sat (atomTraceRanked Unit Probe) (sentence leaveFirst leaveSecond) := fun holds =>
  exits_apart ((rankedValid_branching_iff_atomTrace separable (entryOf leaveFirst.graph)
    (entryOf leaveSecond.graph) (branching_graph leaveFirst) (branching_graph leaveSecond)).mpr holds)

/-- Under one tag, the same payload at a different exit. -/
example : ¬ RankedValid false (sentence split merged) := fun valid => by
  have same := (rankedValid_caseTree_iff separable split merged).mp valid
  simp at same

/-- In a nested arm, the same fresh reply atom at a different exit. -/
example : ¬ RankedValid false (sentence deep deepSecond) := fun valid => by
  have same := (rankedValid_caseTree_iff separable deep deepSecond).mp valid
  simp [ExitAt.term, argTerm] at same

/-! ## The returned atom is observed at an unchanged exit -/

/-- In a nested arm, the fresh reply atom and the outer payload at the
same exit. -/
example : ¬ RankedValid false (sentence deep deepOuter) := fun valid => by
  have same := (rankedValid_caseTree_iff separable deep deepOuter).mp valid
  simp [ExitAt.term, argTerm] at same

/-! ## A valid sentence at the two exits

The second graph is read back from the operand emitted by the first. -/

private def deepAgain : CheckedTable Probe older exits :=
  CheckedTable.ofLetCase (List.cons_ne_nil _ _) deep.graph.toLetCase.2

private theorem again_branching : Branching (emitted (P := atomSig Unit Probe) (entryOf deepAgain)) :=
  Branching.congr (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) deep.graph.toLetCase.2)
    (branching_graph deep)

private theorem again_valid : RankedValid false (sentenceOf (entryOf deep.graph) (entryOf deepAgain)) :=
  (rankedValid_branching_iff separable (entryOf deep.graph) (entryOf deepAgain) (branching_graph deep)
    again_branching).mpr (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) deep.graph.toLetCase.2).symm

/-- The two graphs have the same ordered-exit arrow at the ordered trace
model with atoms. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Probe)) (atomTraceModel Unit Probe) (entryOf deep.graph) =
    denoteRanked (traceJ (α := Unit) (Φ := Probe)) (atomTraceModel Unit Probe) (entryOf deepAgain) :=
  (rankedValid_branching_iff_atomTrace separable (entryOf deep.graph) (entryOf deepAgain)
    (branching_graph deep) again_branching).mp again_valid

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
