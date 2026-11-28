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
open scoped LetSeq.StraightLine.Structural Tagged Binary

/-! ## The direct spelling

There is one atom. The primitive takes one atom and replies with one atom
under the left or the right tag. Two older atoms are captured. The exits
are a pair of atoms, one atom, and a pair of atoms again. Every tree here
cases on the request itself, and no slot holds a reply. -/

private inductive Probe | probe

local instance : BinarySignature Unit Probe := ⟨fun _ => .atom (), fun _ => (), fun _ => ()⟩

private abbrev tok : Ty Unit := .base ()
private abbrev pairTy : Ty Unit := .product tok tok
private abbrev older : BoundCtx (Ty Unit) 2 := (BoundCtx.snoc .nil tok).snoc tok
private abbrev Term (n : Nat) := LetCase.LocallyNameless.Tm Empty Probe n

private theorem separable : Separable older := separable_atoms (.snoc (.snoc .nil ()) ())

private abbrev exits : List (Ty Unit) := [pairTy, tok, pairTy]
private abbrev pairFirst : ExitAt exits pairTy := .here
private abbrev single : ExitAt exits tok := .there .here
private abbrev pairLater : ExitAt exits pairTy := .there (.there .here)

private abbrev earlier : Slot older tok := ⟨1, rfl⟩
private abbrev later : Slot older tok := ⟨0, rfl⟩

/-- Under one arm: the payload and the two older captures. -/
private abbrev armCtx : BoundCtx (Ty Unit) 3 := older.snoc tok
private abbrev payload : Slot armCtx tok := ⟨0, rfl⟩
private abbrev laterIn : Slot armCtx tok := ⟨1, rfl⟩
private abbrev earlierIn : Slot armCtx tok := ⟨2, rfl⟩

/-- Two arms deep: the fresh payload, the outer payload and the captures. -/
private abbrev innerCtx : BoundCtx (Ty Unit) 4 := armCtx.snoc tok
private abbrev fresh : Slot innerCtx tok := ⟨0, rfl⟩
private abbrev outer : Slot innerCtx tok := ⟨1, rfl⟩
private abbrev earlierDeep : Slot innerCtx tok := ⟨3, rfl⟩

/-! ## A nested effectful case

Case on a request on the earlier capture. Under the left tag, case on a
request on the payload. The inner left arm returns, at the first pair
exit, the fresh reply atom paired with the earlier capture. The inner
right arm returns the outer payload and the outer right arm its payload,
both at the atom exit. -/

private def deep : DirectTree older exits
    (.case (.op Probe.probe (.bv 1))
      (.case (.op Probe.probe (.bv 0)) (.inl (.pair (.bv 0) (.bv 3))) (.inr (.inl (.bv 1))))
      (.inr (.inl (.bv 0))) : Term 2) :=
  .ask Probe.probe (.atom earlier)
    (.ask Probe.probe (.atom payload) (.ret pairFirst (.pair (.atom fresh) (.atom earlierDeep)))
      (.ret single (.atom outer)))
    (.ret single (.atom payload))

/-- Its normal form binds each reply and cases on the bound slot. The two
requests are in the same order with the same arguments. The exits are the
same. The fresh payload and the earlier capture are the same slots, now
counted past the two reply slots. -/
private abbrev deepNormal : Term 2 :=
  .let₁ (.op Probe.probe (.bv 1))
    (.case (.bv 0)
      (.let₁ (.op Probe.probe (.bv 0))
        (.case (.bv 0) (.inl (.pair (.bv 0) (.bv 5))) (.inr (.inl (.bv 2)))))
      (.inr (.inl (.bv 0))))

example : (deep.normal (.id older)).1 = deepNormal := rfl

/-- The native equation between the two spellings of this tree. -/
example : Equiv false Γ₀ older
    (.case (.op Probe.probe (.bv 1))
      (.case (.op Probe.probe (.bv 0)) (.inl (.pair (.bv 0) (.bv 3))) (.inr (.inl (.bv 1))))
      (.inr (.inl (.bv 0))) : Term 2)
    deepNormal (packedExitType exits) :=
  direct_equiv_normal deep

/-- The law at the outer request alone: both arms are weakened past the
bound reply. -/
example : Equiv false Γ₀ older
    (.case (.op Probe.probe (.bv 1))
      (.case (.op Probe.probe (.bv 0)) (.inl (.pair (.bv 0) (.bv 3))) (.inr (.inl (.bv 1))))
      (.inr (.inl (.bv 0))) : Term 2)
    (.let₁ (.op Probe.probe (.bv 1))
      (.case (.bv 0)
        (.case (.op Probe.probe (.bv 0)) (.inl (.pair (.bv 0) (.bv 4))) (.inr (.inl (.bv 1))))
        (.inr (.inl (.bv 0)))))
    (packedExitType exits) :=
  ask_case_bind Probe.probe (.atom earlier)
    (DirectTree.ask Probe.probe (.atom payload) (.ret pairFirst (.pair (.atom fresh) (.atom earlierDeep)))
      (.ret single (.atom outer))).typing.toHasType
    (DirectTree.ret (Φ := Probe) single (.atom payload)).typing.toHasType

/-! ## Variants in the direct spelling -/

/-- The two components of the returned pair exchanged. -/
private def deepOrder : DirectTree older exits
    (.case (.op Probe.probe (.bv 1))
      (.case (.op Probe.probe (.bv 0)) (.inl (.pair (.bv 3) (.bv 0))) (.inr (.inl (.bv 1))))
      (.inr (.inl (.bv 0))) : Term 2) :=
  .ask Probe.probe (.atom earlier)
    (.ask Probe.probe (.atom payload) (.ret pairFirst (.pair (.atom earlierDeep) (.atom fresh)))
      (.ret single (.atom outer)))
    (.ret single (.atom payload))

/-- The fresh reply atom replaced by the outer payload. -/
private def deepComponent : DirectTree older exits
    (.case (.op Probe.probe (.bv 1))
      (.case (.op Probe.probe (.bv 0)) (.inl (.pair (.bv 1) (.bv 3))) (.inr (.inl (.bv 1))))
      (.inr (.inl (.bv 0))) : Term 2) :=
  .ask Probe.probe (.atom earlier)
    (.ask Probe.probe (.atom payload) (.ret pairFirst (.pair (.atom outer) (.atom earlierDeep)))
      (.ret single (.atom outer)))
    (.ret single (.atom payload))

/-- The same pair returned at the later exit of its type. -/
private def deepExit : DirectTree older exits
    (.case (.op Probe.probe (.bv 1))
      (.case (.op Probe.probe (.bv 0)) (.inr (.inr (.inl (.pair (.bv 0) (.bv 3))))) (.inr (.inl (.bv 1))))
      (.inr (.inl (.bv 0))) : Term 2) :=
  .ask Probe.probe (.atom earlier)
    (.ask Probe.probe (.atom payload) (.ret pairLater (.pair (.atom fresh) (.atom earlierDeep)))
      (.ret single (.atom outer)))
    (.ret single (.atom payload))

/-- Requests on the earlier and then the later capture. -/
private def earlierFirst : DirectTree older exits
    (.case (.op Probe.probe (.bv 1))
      (.case (.op Probe.probe (.bv 1)) (.inr (.inl (.bv 0))) (.inr (.inl (.bv 1))))
      (.inr (.inl (.bv 0))) : Term 2) :=
  .ask Probe.probe (.atom earlier)
    (.ask Probe.probe (.atom laterIn) (.ret single (.atom fresh)) (.ret single (.atom outer)))
    (.ret single (.atom payload))

/-- Requests on the later and then the earlier capture. -/
private def laterFirst : DirectTree older exits
    (.case (.op Probe.probe (.bv 0))
      (.case (.op Probe.probe (.bv 2)) (.inr (.inl (.bv 0))) (.inr (.inl (.bv 1))))
      (.inr (.inl (.bv 0))) : Term 2) :=
  .ask Probe.probe (.atom later)
    (.ask Probe.probe (.atom earlierIn) (.ret single (.atom fresh)) (.ret single (.atom outer)))
    (.ret single (.atom payload))

/-- The normal forms keep the order of the two requests. -/
example : (earlierFirst.normal (.id older)).1 =
    (.let₁ (.op Probe.probe (.bv 1))
      (.case (.bv 0)
        (.let₁ (.op Probe.probe (.bv 2)) (.case (.bv 0) (.inr (.inl (.bv 0))) (.inr (.inl (.bv 2)))))
        (.inr (.inl (.bv 0)))) : Term 2) := rfl

example : (laterFirst.normal (.id older)).1 =
    (.let₁ (.op Probe.probe (.bv 0))
      (.case (.bv 0)
        (.let₁ (.op Probe.probe (.bv 3)) (.case (.bv 0) (.inr (.inl (.bv 0))) (.inr (.inl (.bv 2)))))
        (.inr (.inl (.bv 0)))) : Term 2) := rfl

/-! ## Completeness applied to the direct syntax -/

private abbrev sentence {t u : Term 2} (p : DirectTree older exits t) (q : DirectTree older exits u) :
    RankedEquation (atomSig Unit Probe) :=
  sentenceOf (entryOf p.graph) (entryOf q.graph)

example : (sentence deep deepExit).1.exits = [pairTy, tok, pairTy] := rfl

/-- The exit of the returned pair is observed. -/
private theorem exit_apart : ¬ RankedValid false (sentence deep deepExit) := fun valid => by
  have same := (rankedValid_directTree_iff separable deep deepExit).mp valid
  simp at same

/-- The order of the fresh reply atom and the older capture is observed. -/
example : ¬ RankedValid false (sentence deep deepOrder) := fun valid => by
  have same := (rankedValid_directTree_iff separable deep deepOrder).mp valid
  simp at same

/-- The fresh reply atom is told apart from the outer payload. -/
example : ¬ RankedValid false (sentence deep deepComponent) := fun valid => by
  have same := (rankedValid_directTree_iff separable deep deepComponent).mp valid
  simp at same

/-- The order of the two requests is observed. -/
example : ¬ RankedValid false (sentence earlierFirst laterFirst) := fun valid => by
  have same := (rankedValid_directTree_iff separable earlierFirst laterFirst).mp valid
  simp at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms,
and the model rejects the sentence. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Probe)) (atomTraceModel Unit Probe) (entryOf deep.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Probe)) (atomTraceModel Unit Probe) (entryOf deepExit.graph) :=
  fun same => by
    have terms := (denoteRanked_directTree_iff separable deep deepExit).mp same
    simp at terms

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Probe))
    (atomSig Unit Probe)).Sat (atomTraceRanked Unit Probe) (sentence deep deepExit) := fun holds =>
  exit_apart ((rankedValid_direct_iff_atomTrace separable (entryOf deep.graph) (entryOf deepExit.graph)
    (direct_graph deep) (direct_graph deepExit)).mpr holds)

/-! ## The two spellings are one sentence

The graph read back from the direct tree and the graph read back from its
normal form are valid together, and have the same ordered-exit arrow at
the ordered trace model with atoms. -/

private theorem spellings_valid :
    RankedValid false (sentenceOf (entryOf deep.graph) (entryOf (deep.normal (.id older)).2.graph)) :=
  rankedValid_direct_normal separable deep

example : denoteRanked (traceJ (α := Unit) (Φ := Probe)) (atomTraceModel Unit Probe) (entryOf deep.graph) =
    denoteRanked (traceJ (α := Unit) (Φ := Probe)) (atomTraceModel Unit Probe)
      (entryOf (deep.normal (.id older)).2.graph) :=
  (rankedValid_branching_iff_atomTrace separable (entryOf deep.graph)
    (entryOf (deep.normal (.id older)).2.graph) (branching_of_direct (direct_graph deep))
    (branching_graph (deep.normal (.id older)).2)).mp spellings_valid

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
