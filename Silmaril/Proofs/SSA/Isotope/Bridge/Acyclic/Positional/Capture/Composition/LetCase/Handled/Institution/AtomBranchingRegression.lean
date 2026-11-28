module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetSeq.StraightLine.Structural (Slot Assembly)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
open scoped LetSeq.StraightLine.Structural Tagged

/-! ## A signature with a two-tag atom reply

There is one atom. The primitive takes one atom and replies with one atom
under the first or the second tag. Two older atoms are captured. There is
one exit. -/

private inductive Probe | probe

local instance : TaggedSignature Unit Probe := ⟨fun _ => .atom (), fun _ => [()], fun _ => [[()]]⟩

private abbrev tok : Ty Unit := .base ()
private abbrev replyTy : Ty Unit := .coprod tok tok
private abbrev older : BoundCtx (Ty Unit) 2 := (BoundCtx.snoc .nil tok).snoc tok
private abbrev Term (n : Nat) := LetCase.LocallyNameless.Tm Empty Probe n

private theorem olderAtoms : AtomContext older := .snoc (.snoc .nil ()) ()
private theorem separable : Separable older := separable_atoms olderAtoms

example : instrTrg (τ := Ty Unit) Probe.probe = replyTy := rfl

/-- The earlier and the later of the two older captures. -/
private abbrev earlier : Slot older tok := ⟨1, rfl⟩
private abbrev later : Slot older tok := ⟨0, rfl⟩

/-- Under one arm: the payload, the bound reply, and the two older
captures still in scope. -/
private abbrev armCtx : BoundCtx (Ty Unit) 4 := (older.snoc replyTy).snoc tok
private abbrev payload : Slot armCtx tok := ⟨0, rfl⟩
private abbrev laterIn : Slot armCtx tok := ⟨2, rfl⟩
private abbrev earlierIn : Slot armCtx tok := ⟨3, rfl⟩

/-- Two arms deep: the inner payload, the outer payload and both older
captures are in scope. -/
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

/-! ## Case trees -/

/-- Probe the earlier capture. Return the payload under the first tag and
the earlier capture under the second tag. -/
private def keep : CaseTree .body older [tok]
    (.let₁ (.op Probe.probe (.bv 1)) (.case (.bv 0) (.inl (.bv 0)) (.inl (.bv 3))) : Term 2) :=
  probe earlier (.ret .here (.atom payload)) (.ret .here (.atom earlierIn))

/-- The same request with the two arms exchanged. -/
private def flip : CaseTree .body older [tok]
    (.let₁ (.op Probe.probe (.bv 1)) (.case (.bv 0) (.inl (.bv 3)) (.inl (.bv 0))) : Term 2) :=
  probe earlier (.ret .here (.atom earlierIn)) (.ret .here (.atom payload))

/-- The same request, returning the payload under both tags. -/
private def both : CaseTree .body older [tok]
    (.let₁ (.op Probe.probe (.bv 1)) (.case (.bv 0) (.inl (.bv 0)) (.inl (.bv 0))) : Term 2) :=
  probe earlier (.ret .here (.atom payload)) (.ret .here (.atom payload))

/-- The same arms after probing the later capture. -/
private def other : CaseTree .body older [tok]
    (.let₁ (.op Probe.probe (.bv 0)) (.case (.bv 0) (.inl (.bv 0)) (.inl (.bv 3))) : Term 2) :=
  probe later (.ret .here (.atom payload)) (.ret .here (.atom earlierIn))

/-- Probe the earlier capture, then under the first tag probe the payload
just received. The inner arms return the inner and the outer payload. -/
private def chain :=
  probe (L := [tok]) earlier
    (probe payload (.ret .here (.atom fresh)) (.ret .here (.atom outer)))
    (.ret .here (.atom payload))

/-- Probe the earlier capture and then the later one. -/
private def earlierFirst :=
  probe (L := [tok]) earlier
    (probe laterIn (.ret .here (.atom fresh)) (.ret .here (.atom outer)))
    (.ret .here (.atom payload))

/-- Probe the later capture and then the earlier one. -/
private def laterFirst :=
  probe (L := [tok]) later
    (probe earlierIn (.ret .here (.atom fresh)) (.ret .here (.atom outer)))
    (.ret .here (.atom payload))

/-! ## Sentences between the graphs read back from the trees -/

private abbrev sentence {t u : Term 2} (p : CaseTree .body older [tok] t) (q : CaseTree .body older [tok] u) :
    RankedEquation (atomSig Unit Probe) :=
  sentenceOf (entryOf p.graph) (entryOf q.graph)

/-- Exchanging the arms is observed. -/
private theorem arms_apart : ¬ RankedValid false (sentence keep flip) := fun valid => by
  have same := (rankedValid_caseTree_iff separable keep flip).mp valid
  simp at same

/-- The atom returned under one tag is observed. -/
example : ¬ RankedValid false (sentence keep both) := fun valid => by
  have same := (rankedValid_caseTree_iff separable keep both).mp valid
  simp at same

/-- The older capture used as the request argument is observed. -/
example : ¬ RankedValid false (sentence keep other) := fun valid => by
  have same := (rankedValid_caseTree_iff separable keep other).mp valid
  simp at same

/-- The order of two requests on the two older captures is observed. -/
example : ¬ RankedValid false (sentence earlierFirst laterFirst) := fun valid => by
  have same := (rankedValid_caseTree_iff separable earlierFirst laterFirst).mp valid
  simp at same

/-- A payload used as the next request argument is told apart from an
older capture used there. -/
example : ¬ RankedValid false (sentence chain earlierFirst) := fun valid => by
  have same := (rankedValid_caseTree_iff separable chain earlierFirst).mp valid
  simp at same

/-- The ordered trace model with atoms is a supported model that rejects
the sentence with exchanged arms. -/
example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Probe))
    (atomSig Unit Probe)).Sat (atomTraceRanked Unit Probe) (sentence keep flip) := fun holds =>
  arms_apart ((rankedValid_branching_iff_atomTrace separable (entryOf keep.graph) (entryOf flip.graph)
    (branching_graph keep) (branching_graph flip)).mpr holds)

/-! ## A valid sentence between two graphs

The second graph is read back from the operand emitted by the first. Its
emitted operand is natively equal to the same case tree. -/

private def chainAgain : CheckedTable Probe older [tok] :=
  CheckedTable.ofLetCase (List.cons_ne_nil _ _) chain.graph.toLetCase.2

private theorem again_branching : Branching (emitted (P := atomSig Unit Probe) (entryOf chainAgain)) :=
  Branching.congr (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) chain.graph.toLetCase.2)
    (branching_graph chain)

private theorem again_valid : RankedValid false (sentenceOf (entryOf chain.graph) (entryOf chainAgain)) :=
  (rankedValid_branching_iff separable (entryOf chain.graph) (entryOf chainAgain) (branching_graph chain)
    again_branching).mpr (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) chain.graph.toLetCase.2).symm

/-- The ordered trace model with atoms satisfies it. -/
example : (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Probe))
    (atomSig Unit Probe)).Sat (atomTraceRanked Unit Probe)
      (sentenceOf (entryOf chain.graph) (entryOf chainAgain)) :=
  (rankedValid_branching_iff_atomTrace separable (entryOf chain.graph) (entryOf chainAgain)
    (branching_graph chain) again_branching).mp again_valid

/-- The reduction at a request: `keep` and `both` have the same request,
so their traces agree exactly when their continuations agree at every
reply. -/
example (ρ : Isotope.Semantics.BoundEnv (LetSeq.StraightLine.Structural.Value (α := Unit)) older) :
    LetCase.Structural.Reply.run keep.typing ρ = LetCase.Structural.Reply.run both.typing ρ ↔
      ∀ w : LetSeq.StraightLine.Structural.Value (α := Unit) replyTy,
        LetCase.Structural.Reply.run
            (arms (L := [tok]) (β := older) (.ret .here (.atom payload)) (.ret .here (.atom earlierIn))).typing
            (ρ.snoc w) =
          LetCase.Structural.Reply.run
            (arms (L := [tok]) (β := older) (.ret .here (.atom payload)) (.ret .here (.atom payload))).typing
            (ρ.snoc w) :=
  ask_run_eq_iff Probe.probe (.atom earlier) _ _ ρ

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
