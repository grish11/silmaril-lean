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

/-! ## A pair held across a later request

There is one atom. `both` takes one atom and replies with a pair of atoms
under its one tag. `ping` takes one atom and replies with one atom.
`fetch` takes a pair of atoms and replies with a pair of atoms or with one
atom. Two older atoms are captured. The exits are a pair of atoms and one
atom. -/

private inductive Op | both | ping | fetch

local instance : TaggedSignature Unit Op where
  argument
    | .both => .atom ()
    | .ping => .atom ()
    | .fetch => .pair (.atom ()) (.atom ())
  first
    | .both => [(), ()]
    | .ping => [()]
    | .fetch => [(), ()]
  others
    | .both => []
    | .ping => []
    | .fetch => [[()]]

private abbrev tok : Ty Unit := .base ()
private abbrev pairTy : Ty Unit := .product tok tok
private abbrev older : BoundCtx (Ty Unit) 2 := (BoundCtx.snoc .nil tok).snoc tok
private abbrev Term (n : Nat) := LetCase.LocallyNameless.Tm Empty Op n

private theorem separable : Separable older := separable_atoms (.snoc (.snoc .nil ()) ())

private abbrev exits : List (Ty Unit) := [pairTy, tok]
private abbrev pairExit : ExitAt exits pairTy := .here
private abbrev atomExit : ExitAt exits tok := .there .here

private abbrev earlier : Slot older tok := ⟨1, rfl⟩
private abbrev later : Slot older tok := ⟨0, rfl⟩

/-! ## The bound reply of `both` held across `ping`

Ask `both` on the earlier capture and bind the pair. Do not destructure it
yet. Ask `ping` on the later capture and bind its reply `c`. Then
destructure the pair into `a` and `b`, and return a pair at the pair
exit. -/

/-- Under the held pair: the pair and the two captures. -/
private abbrev underPair : BoundCtx (Ty Unit) 3 := older.snoc pairTy
private abbrev laterUnder : Slot underPair tok := ⟨1, rfl⟩
private abbrev earlierUnder : Slot underPair tok := ⟨2, rfl⟩

/-- After the destructuring: `b`, `a`, `c`, the pair, and the two captures. -/
private abbrev heldCtx : BoundCtx (Ty Unit) 6 := (((older.snoc pairTy).snoc tok).snoc tok).snoc tok
private abbrev compB : Slot heldCtx tok := ⟨0, rfl⟩
private abbrev compA : Slot heldCtx tok := ⟨1, rfl⟩
private abbrev replyC : Slot heldCtx tok := ⟨2, rfl⟩
private abbrev earlierIn : Slot heldCtx tok := ⟨5, rfl⟩

/-- The tree returning a chosen pair. -/
private def heldWith (first second : Slot heldCtx tok) : Spelled older exits
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.ping (.bv 1))
        (.let₂ (.bv 1) (.inl (.pair (.bv first.1) (.bv second.1))))) : Term 2) :=
  .ask Op.both (.atom earlier)
    (.bind (.only [(), ()]
      (.hold [(), ()]
        (.ask Op.ping
          (.atom laterUnder)
          (.bind [()]
            (.atom (.step (.atom (.done (.ret pairExit (.pair (.atom first) (.atom second))))))))))))

/-- The normal form with a chosen returned pair. The pair is destructured
before `ping`. -/
private abbrev normalWith (first second : Fin 6) : Term 2 :=
  .let₁ (.op Op.both (.bv 1))
    (.let₂ (.bv 0)
      (.let₁ (.op Op.ping (.bv 3)) (.inl (.pair (.bv first) (.bv second)))))

/-- Return the first component of the held pair with the later reply. -/
private abbrev held := heldWith compA replyC

/-- The spelled term: `ping` is asked while the pair is still one slot. -/
example : Spelled older exits
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.ping (.bv 1)) (.let₂ (.bv 1) (.inl (.pair (.bv 1) (.bv 2))))) : Term 2) := held

/-- Its normal form. `both` and `ping` each occur once, in the same order,
with the same arguments: `ping` is still asked on the later capture, now
counted past the two components. The returned pair is the same two slots. -/
example : (held.normal (.id older)).1 = normalWith 2 0 := rfl

/-- The native equation between the spelling and its normal form. -/
example : Equiv false Γ₀ older
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.ping (.bv 1)) (.let₂ (.bv 1) (.inl (.pair (.bv 1) (.bv 2))))) : Term 2)
    (.let₁ (.op Op.both (.bv 1))
      (.let₂ (.bv 0) (.let₁ (.op Op.ping (.bv 3)) (.inl (.pair (.bv 2) (.bv 0))))))
    (packedExitType exits) :=
  spelled_equiv_normal held

/-- The commuting equation alone, under the bound pair: the pattern let
moves in front of the request, and the request is weakened past the two
components. -/
example : Equiv false Γ₀ (older.snoc pairTy)
    (.let₁ (.op Op.ping (.bv 1)) (.let₂ (.bv 1) (.inl (.pair (.bv 1) (.bv 2)))) : Term 3)
    (.let₂ (.bv 0) (.let₁ (.op Op.ping (.bv 3)) (.inl (.pair (.bv 2) (.bv 0)))))
    (packedExitType exits) :=
  let_pair_comm (0 : Fin 3) rfl
    (LetCase.LocallyNameless.Derivation.op (f := Op.ping)
      (argTyping (Φ := Op) (Assembly.atom (β := older.snoc pairTy) ⟨1, rfl⟩))).toHasType
    (Spelled.ret (Φ := Op) pairExit (.pair (.atom compA) (.atom replyC))).typing.toHasType

/-! ## Variants -/

private abbrev otherComponent := heldWith compB replyC
private abbrev otherOrder := heldWith replyC compA
private abbrev withCapture := heldWith compA earlierIn

example : (otherComponent.normal (.id older)).1 = normalWith 1 0 := rfl
example : (otherOrder.normal (.id older)).1 = normalWith 0 2 := rfl
example : (withCapture.normal (.id older)).1 = normalWith 2 5 := rfl

/-- The eager spelling: destructure the pair at once, then ask `ping`. It
is its own normal form, and it is the normal form of the held spelling. -/
private def eager : Spelled older exits (normalWith 2 0) :=
  .ask Op.both (.atom earlier)
    (.bind (.only [(), ()]
      (.pair () () []
        (.atom ()
          (.ask Op.ping (.atom ⟨3, rfl⟩)
            (.bind (.only [()]
              (.atom () (.ret (β := heldCtx) pairExit (.pair (.atom ⟨2, rfl⟩) (.atom ⟨0, rfl⟩)))))))))))

example : (eager.normal (.id older)).1 = normalWith 2 0 := rfl

/-! ## Ranked validity -/

private abbrev sentence {t u : Term 2} (p : Spelled older exits t) (q : Spelled older exits u) :
    RankedEquation (atomSig Unit Op) :=
  sentenceOf (entryOf p.graph) (entryOf q.graph)

example : (sentence held eager).1.exits = [pairTy, tok] := rfl

/-- Holding the pair across the request and destructuring it at once are
one sentence: the two graphs are valid together. -/
private theorem held_eager : RankedValid false (sentence held eager) :=
  (rankedValid_spelledTree_iff separable held eager).mpr rfl

/-- They have the same ordered-exit arrow at the ordered trace model with
atoms. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf held.graph) =
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf eager.graph) :=
  (denoteRanked_spelledTree_iff separable held eager).mpr rfl

/-- Which component of the held pair is returned is observed. -/
private theorem component_apart : ¬ RankedValid false (sentence held otherComponent) := fun valid => by
  have same : normalWith 2 0 = normalWith 1 0 :=
    (rankedValid_spelledTree_iff separable held otherComponent).mp valid
  simp at same

/-- The order of the old component and the new reply is observed. -/
example : ¬ RankedValid false (sentence held otherOrder) := fun valid => by
  have same : normalWith 2 0 = normalWith 0 2 :=
    (rankedValid_spelledTree_iff separable held otherOrder).mp valid
  simp at same

/-- The new reply and an older capture are told apart. -/
example : ¬ RankedValid false (sentence held withCapture) := fun valid => by
  have same : normalWith 2 0 = normalWith 2 5 :=
    (rankedValid_spelledTree_iff separable held withCapture).mp valid
  simp at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms,
and the model rejects the sentence. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf held.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf otherComponent.graph) :=
  fun same => by
    have terms : normalWith 2 0 = normalWith 1 0 :=
      (denoteRanked_spelledTree_iff separable held otherComponent).mp same
    simp at terms

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence held otherComponent) := fun holds =>
  component_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf held.graph)
    (entryOf otherComponent.graph) (spelled_graph held) (spelled_graph otherComponent)).mpr holds)

/-! ## A pair arm held across a request

Ask `fetch` on the two captures and case on the request. The payload of
the pair tag is held across `ping` on the earlier capture, then
destructured, and its second component is returned with the reply of
`ping`. -/

private def armHeld : Spelled older exits
    (.case (.op Op.fetch (.pair (.bv 1) (.bv 0)))
      (.let₁ (.op Op.ping (.bv 2)) (.let₂ (.bv 1) (.inl (.pair (.bv 0) (.bv 2)))))
      (.inr (.inl (.bv 0))) : Term 2) :=
  .ask Op.fetch (.pair (.atom earlier) (.atom later))
    (.branch [(), ()] [()] []
      (.hold [(), ()]
        (.ask Op.ping
          (.atom earlierUnder)
          (.bind [()]
            (.atom (.step (.atom (.done (.ret pairExit (.pair (.atom compB) (.atom replyC))))))))))
      (.only [()] (.atom () (.ret (β := (older.snoc tok)) atomExit (.atom ⟨0, rfl⟩)))))

/-- Its normal form binds the reply of `fetch`, cases on it, and
destructures the pair arm before `ping`. `ping` is still asked once, on
the earlier capture. -/
example : (armHeld.normal (.id older)).1 =
    (.let₁ (.op Op.fetch (.pair (.bv 1) (.bv 0)))
      (.case (.bv 0)
        (.let₂ (.bv 0) (.let₁ (.op Op.ping (.bv 5)) (.inl (.pair (.bv 1) (.bv 0)))))
        (.inr (.inl (.bv 0)))) : Term 2) := rfl

/-- The graph of the spelling and the graph of its normal form are valid
together. -/
example : RankedValid false
    (sentenceOf (entryOf armHeld.graph) (entryOf (armHeld.normal (.id older)).2.graph)) :=
  rankedValid_spelled_normal separable armHeld

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
