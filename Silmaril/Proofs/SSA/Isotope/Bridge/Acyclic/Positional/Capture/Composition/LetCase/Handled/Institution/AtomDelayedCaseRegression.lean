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

/-! ## A reply with two tags inspected after a later request

There is one atom. `pick` takes one atom and replies with one of two tags:
the first carries a pair of atoms and the second one atom. `ping` takes one
atom and replies with one atom. `both` takes one atom and replies with a
pair of atoms. Two older atoms are captured. The exits are a pair of atoms
and one atom. -/

private inductive Op | both | pick | ping

local instance : TaggedSignature Unit Op where
  argument
    | .both => .atom ()
    | .pick => .atom ()
    | .ping => .atom ()
  first
    | .both => [(), ()]
    | .pick => [(), ()]
    | .ping => [()]
  others
    | .pick => [[()]]
    | _ => []

private abbrev tok : Ty Unit := .base ()
private abbrev pairTy : Ty Unit := .product tok tok
private abbrev sumTy : Ty Unit := .coprod pairTy tok
private abbrev older : BoundCtx (Ty Unit) 2 := (BoundCtx.snoc .nil tok).snoc tok
private abbrev Term (n : Nat) := LetCase.LocallyNameless.Tm Empty Op n

private theorem separable : Separable older := separable_atoms (.snoc (.snoc .nil ()) ())

private abbrev exits : List (Ty Unit) := [pairTy, tok]
private abbrev pairExit : ExitAt exits pairTy := .here

private abbrev later : Slot older tok := ⟨0, rfl⟩
private abbrev earlier : Slot older tok := ⟨1, rfl⟩

/-! ## The chain

Ask `pick` on the later capture and bind its reply, a slot of sum type.
Ask `ping` on an older capture, with reply `c`. Only then case on the reply
of `pick`. Under the first tag, with payload a pair, destructure it into
`x₁` and `x₂` and return a pair. Under the second tag, with payload `y`,
return a pair. The reply of `pick` is one slot across `ping`, and `ping`
cannot read it: its argument is an atom slot. -/

/-- Under the stored reply: the reply and the two captures. The reply has
sum type, so it is not an atom slot. -/
private abbrev underS : BoundCtx (Ty Unit) 3 := older.snoc sumTy
private abbrev laterS : Slot underS tok := ⟨1, rfl⟩
private abbrev earlierS : Slot underS tok := ⟨2, rfl⟩

/-- The leaf under the first tag, with the reply of `ping` beneath the
components: `x₂`, `x₁`, `c`, the payload, the reply and the two captures. -/
private abbrev leafL : BoundCtx (Ty Unit) 7 := (((underS.snoc pairTy).snoc tok).snoc tok).snoc tok

/-- The leaf under the second tag: `c`, `y`, the reply and the two
captures. -/
private abbrev leafR : BoundCtx (Ty Unit) 5 := (underS.snoc tok).snoc tok

/-! The arms of the delayed case are stated with the reply of `ping` as the
newest slot, the payload beneath it. In the term the payload is newest. -/

private def armL :
    SpelledStackTags (Φ := Op) [[(), ()]] [[()]] (underS.snoc pairTy) (.cons ⟨0, rfl⟩ .nil) exits
      (.let₂ (.bv 1) (.inl (.pair (.bv 1) (.bv 2))) : Term 5) :=
  .bind [()]
    (.atom
      (.step (.atom (.done (.ret pairExit (.pair (.atom (β := leafL) ⟨1, rfl⟩) (.atom ⟨2, rfl⟩)))))))

private def armR :
    SpelledLaterTags (Φ := Op) [] [[()]] Op.ping underS .nil exits
      (.inl (.pair (.bv 1) (.bv 0)) : Term 5) :=
  .only [()]
    (.bind [()]
      (.atom (.atom (.done (.ret pairExit (.pair (.atom (β := leafR) ⟨1, rfl⟩) (.atom ⟨0, rfl⟩)))))))

/-- The tree with a chosen argument of `ping`. -/
private def chainWith (arg : Slot underS tok) :
    Spelled older exits
      (.let₁ (.op Op.pick (.bv 0))
        (.let₁ (.op Op.ping (.bv arg.1))
          (.case (.bv 1)
            (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
            (.inl (.pair (.bv 0) (.bv 1))))) : Term 2) :=
  .chain
    (.ask Op.pick (.atom later)
      (.later (tags := [[(), ()], [()]]) Op.ping (Assembly.atom arg)
        (.split (h := Op.ping) (holds := .nil) [(), ()] [()] [] armL armR)))

/-- The normal form with chosen arguments of `ping` and chosen returned
pairs. The case on the reply of `pick` directly follows `pick`, and `ping`
is written once in each arm. -/
private abbrev normalWith (argL : Fin 6) (argR : Fin 4) (fl sl : Fin 7) (fr sr : Fin 5) : Term 2 :=
  .let₁ (.op Op.pick (.bv 0))
    (.case (.bv 0)
      (.let₂ (.bv 0) (.let₁ (.op Op.ping (.bv argL)) (.inl (.pair (.bv fl) (.bv sl)))))
      (.let₁ (.op Op.ping (.bv argR)) (.inl (.pair (.bv fr) (.bv sr)))))

/-- `ping` takes the earlier capture. Under the first tag the first
component of the payload is returned with the reply of `ping`, and under
the second tag the payload with the reply of `ping`. -/
private abbrev chain := chainWith earlierS

/-- The spelled term: `ping` is asked between `pick` and the case on its
reply. -/
example : Spelled older exits
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.ping (.bv 2))
        (.case (.bv 1)
          (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
          (.inl (.pair (.bv 0) (.bv 1))))) : Term 2) := chain

/-- Its normal form. `pick` and `ping` are asked in that order on either
run. -/
private theorem chain_normal : (chain.normal (.id older)).1 = normalWith 5 3 2 0 1 0 := rfl

/-- The native equation between the spelling and its normal form. -/
example : Equiv false Γ₀ older
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.ping (.bv 2))
        (.case (.bv 1)
          (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
          (.inl (.pair (.bv 0) (.bv 1))))) : Term 2)
    (.let₁ (.op Op.pick (.bv 0))
      (.case (.bv 0)
        (.let₂ (.bv 0) (.let₁ (.op Op.ping (.bv 5)) (.inl (.pair (.bv 2) (.bv 0)))))
        (.let₁ (.op Op.ping (.bv 3)) (.inl (.pair (.bv 1) (.bv 0))))))
    (packedExitType exits) :=
  spelled_equiv_normal chain

/-- In a larger context the normal form is the renamed normal form. -/
example : (chain.normal (BoundCtx.Renaming.succ older tok)).1 =
    (normalWith 5 3 2 0 1 0).rename Fin.succ :=
  spelled_normal_rename_term chain (.id older) (BoundCtx.Renaming.succ older tok)

/-! ## Variants -/

/-- `ping` takes the later capture. -/
private abbrev otherArg := chainWith laterS

private def armL₁ :
    SpelledStackTags (Φ := Op) [[(), ()]] [[()]] (underS.snoc pairTy) (.cons ⟨0, rfl⟩ .nil) exits
      (.let₂ (.bv 1) (.inl (.pair (.bv 0) (.bv 2))) : Term 5) :=
  .bind [()]
    (.atom
      (.step (.atom (.done (.ret pairExit (.pair (.atom (β := leafL) ⟨0, rfl⟩) (.atom ⟨2, rfl⟩)))))))

private def armR₁ :
    SpelledLaterTags (Φ := Op) [] [[()]] Op.ping underS .nil exits
      (.inl (.pair (.bv 1) (.bv 0)) : Term 5) :=
  .only [()]
    (.bind [()]
      (.atom (.atom (.done (.ret pairExit (.pair (.atom (β := leafR) ⟨1, rfl⟩) (.atom ⟨0, rfl⟩)))))))

/-- Under the first tag the other component of the payload is returned. -/
private def otherLeft :
    Spelled older exits
      (.let₁ (.op Op.pick (.bv 0))
        (.let₁ (.op Op.ping (.bv 2))
          (.case (.bv 1)
            (.let₂ (.bv 0) (.inl (.pair (.bv 0) (.bv 3))))
            (.inl (.pair (.bv 0) (.bv 1))))) : Term 2) :=
  .chain
    (.ask Op.pick (.atom later)
      (.later (tags := [[(), ()], [()]]) Op.ping (Assembly.atom earlierS)
        (.split (h := Op.ping) (holds := .nil) [(), ()] [()] [] armL₁ armR₁)))

private def armL₂ :
    SpelledStackTags (Φ := Op) [[(), ()]] [[()]] (underS.snoc pairTy) (.cons ⟨0, rfl⟩ .nil) exits
      (.let₂ (.bv 1) (.inl (.pair (.bv 1) (.bv 2))) : Term 5) :=
  .bind [()]
    (.atom
      (.step (.atom (.done (.ret pairExit (.pair (.atom (β := leafL) ⟨1, rfl⟩) (.atom ⟨2, rfl⟩)))))))

private def armR₂ :
    SpelledLaterTags (Φ := Op) [] [[()]] Op.ping underS .nil exits
      (.inl (.pair (.bv 0) (.bv 1)) : Term 5) :=
  .only [()]
    (.bind [()]
      (.atom (.atom (.done (.ret pairExit (.pair (.atom (β := leafR) ⟨0, rfl⟩) (.atom ⟨1, rfl⟩)))))))

/-- Under the second tag the two returned atoms are exchanged. -/
private def otherRight :
    Spelled older exits
      (.let₁ (.op Op.pick (.bv 0))
        (.let₁ (.op Op.ping (.bv 2))
          (.case (.bv 1)
            (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
            (.inl (.pair (.bv 1) (.bv 0))))) : Term 2) :=
  .chain
    (.ask Op.pick (.atom later)
      (.later (tags := [[(), ()], [()]]) Op.ping (Assembly.atom earlierS)
        (.split (h := Op.ping) (holds := .nil) [(), ()] [()] [] armL₂ armR₂)))

example : (otherArg.normal (.id older)).1 = normalWith 4 2 2 0 1 0 := rfl
example : (otherLeft.normal (.id older)).1 = normalWith 5 3 1 0 1 0 := rfl
example : (otherRight.normal (.id older)).1 = normalWith 5 3 2 0 0 1 := rfl

/-! ## The eager spellings

The reply of `pick` is cased on at once, and `ping` is written in each
arm. -/

private abbrev openL : BoundCtx (Ty Unit) 6 := ((underS.snoc pairTy).snoc tok).snoc tok
private abbrev openR : BoundCtx (Ty Unit) 4 := underS.snoc tok

private def eagerLeftLeaf :=
  Spelled.ret (Φ := Op) (β := openL.snoc tok) pairExit (.pair (.atom ⟨2, rfl⟩) (.atom ⟨0, rfl⟩))

private def eagerRightLeaf :=
  Spelled.ret (Φ := Op) (β := openR.snoc tok) pairExit (.pair (.atom ⟨1, rfl⟩) (.atom ⟨0, rfl⟩))

private def eagerLeft :=
  Spelled.ask Op.ping (.atom (β := openL) ⟨5, rfl⟩) (.bind (.only [()] (.atom () eagerLeftLeaf)))

private def eagerRight (arg : Slot openR tok) :=
  Spelled.ask Op.ping (.atom arg) (.bind (.only [()] (.atom () eagerRightLeaf)))

/-- The eager spelling with `ping` on the earlier capture in both arms. It
is the normal form of the delayed chain. -/
private def eager : Spelled older exits (normalWith 5 3 2 0 1 0) :=
  .ask Op.pick (.atom later)
    (.bind (.split [(), ()] [()] []
      (.pair () () [] (.atom () eagerLeft)) (.only [()] (.atom () (eagerRight ⟨3, rfl⟩)))))

private theorem eager_normal : (eager.normal (.id older)).1 = normalWith 5 3 2 0 1 0 := rfl

/-- An eager tree whose arms ask different requests: `ping` on the earlier
capture under the first tag and on the later capture under the second. No
delayed chain has this normal form, since the delayed request is one term
for both tags. -/
private def skewed : Spelled older exits (normalWith 5 2 2 0 1 0) :=
  .ask Op.pick (.atom later)
    (.bind (.split [(), ()] [()] []
      (.pair () () [] (.atom () eagerLeft)) (.only [()] (.atom () (eagerRight ⟨2, rfl⟩)))))

private theorem skewed_normal : (skewed.normal (.id older)).1 = normalWith 5 2 2 0 1 0 := rfl

/-! ## A delayed inspection under a held pair

Ask `both` and hold its pair. Ask `pick`, then `ping` on the earlier
capture, then case on the reply of `pick`. Each arm destructures the held
pair. Under the first tag the first component of the held pair is returned
with the first component of the payload, and under the second tag the
second component of the held pair with the payload. -/

private abbrev underP : BoundCtx (Ty Unit) 3 := older.snoc pairTy
private abbrev underPS : BoundCtx (Ty Unit) 4 := underP.snoc sumTy
private abbrev heldLeafL : BoundCtx (Ty Unit) 10 :=
  (((((underPS.snoc pairTy).snoc tok).snoc tok).snoc tok).snoc tok).snoc tok
private abbrev heldLeafR : BoundCtx (Ty Unit) 8 := (((underPS.snoc tok).snoc tok).snoc tok).snoc tok

private def heldArmL :
    SpelledStackTags (Φ := Op) [[(), ()], [(), ()]] [[()]] (underPS.snoc pairTy)
      (.cons ⟨0, rfl⟩ (.cons ⟨2, rfl⟩ .nil)) exits
      (.let₂ (.bv 1) (.let₂ (.bv 5) (.inl (.pair (.bv 1) (.bv 3)))) : Term 6) :=
  .bind [()]
    (.atom
      (.step
        (.atom
          (.step
            (.atom
              (.done (.ret pairExit (.pair (.atom (β := heldLeafL) ⟨1, rfl⟩) (.atom ⟨3, rfl⟩)))))))))

private def heldArmR :
    SpelledLaterTags (Φ := Op) [[(), ()]] [[()]] Op.ping underPS (.cons ⟨1, rfl⟩ .nil) exits
      (.let₂ (.bv 3) (.inl (.pair (.bv 0) (.bv 3))) : Term 6) :=
  .only [()]
    (.bind [()]
      (.atom
        (.atom
          (.step
            (.atom
              (.done (.ret pairExit (.pair (.atom (β := heldLeafR) ⟨0, rfl⟩) (.atom ⟨3, rfl⟩)))))))))

private def held : Spelled older exits
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.pick (.bv 1))
        (.let₁ (.op Op.ping (.bv 3))
          (.case (.bv 1)
            (.let₂ (.bv 0) (.let₂ (.bv 5) (.inl (.pair (.bv 1) (.bv 3)))))
            (.let₂ (.bv 3) (.inl (.pair (.bv 0) (.bv 2))))))) : Term 2) :=
  .ask Op.both (.atom earlier)
    (.bind
      (.only [(), ()]
        (.hold [(), ()]
          (.ask Op.pick (.atom (β := underP) ⟨1, rfl⟩)
            (.later (tags := [[(), ()], [()]]) Op.ping (Assembly.atom (β := underPS) ⟨3, rfl⟩)
              (.split (stack := [[(), ()]]) (h := Op.ping) (Δ := underP) (holds := .cons ⟨0, rfl⟩ .nil) [(), ()] [()] [] heldArmL heldArmR))))))

/-- The held pair is destructured before `pick`. The case is on the reply
of `pick`, right after it, and `ping` is asked in each arm. -/
example : (held.normal (.id older)).1 =
    (.let₁ (.op Op.both (.bv 1))
      (.let₂ (.bv 0)
        (.let₁ (.op Op.pick (.bv 3))
          (.case (.bv 0)
            (.let₂ (.bv 0) (.let₁ (.op Op.ping (.bv 8)) (.inl (.pair (.bv 6) (.bv 2)))))
            (.let₁ (.op Op.ping (.bv 6)) (.inl (.pair (.bv 3) (.bv 1))))))) : Term 2) := rfl

/-! ## Ranked validity and ordered-exit arrows -/

private abbrev sentence {t u : Term 2} (p : Spelled older exits t) (q : Spelled older exits u) :
    RankedEquation (atomSig Unit Op) :=
  sentenceOf (entryOf p.graph) (entryOf q.graph)

/-- The delayed chain and the eager spelling are one sentence: moving the
tag test in front of `ping` and writing `ping` in each arm does not change
the ranked meaning. -/
private theorem chain_eager : RankedValid false (sentence chain eager) :=
  (rankedValid_spelledTree_iff separable chain eager).mpr (chain_normal.trans eager_normal.symm)

/-- They have the same ordered-exit arrow at the ordered trace model with
atoms. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) =
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf eager.graph) :=
  (denoteRanked_spelledTree_iff separable chain eager).mpr (chain_normal.trans eager_normal.symm)

/-- Which older capture the delayed request takes. -/
private theorem arg_apart : ¬ RankedValid false (sentence chain otherArg) := fun valid => by
  have same : normalWith 5 3 2 0 1 0 = normalWith 4 2 2 0 1 0 :=
    (rankedValid_spelledTree_iff separable chain otherArg).mp valid
  simp at same

/-- The branch of the first tag is observed: a changed component. -/
private theorem left_apart : ¬ RankedValid false (sentence chain otherLeft) := fun valid => by
  have same : normalWith 5 3 2 0 1 0 = normalWith 5 3 1 0 1 0 :=
    (rankedValid_spelledTree_iff separable chain otherLeft).mp valid
  simp at same

/-- The branch of the second tag is observed: a changed order. -/
private theorem right_apart : ¬ RankedValid false (sentence chain otherRight) := fun valid => by
  have same : normalWith 5 3 2 0 1 0 = normalWith 5 3 2 0 0 1 :=
    (rankedValid_spelledTree_iff separable chain otherRight).mp valid
  simp at same

/-- The request under the second tag alone is observed: the delayed chain
differs from the eager tree whose arms ask different requests. -/
example : ¬ RankedValid false (sentence chain skewed) := fun valid => by
  have same : normalWith 5 3 2 0 1 0 = normalWith 5 2 2 0 1 0 :=
    (chain_normal.symm.trans ((rankedValid_spelledTree_iff separable chain skewed).mp valid)).trans
      skewed_normal
  simp at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms,
and the model rejects each sentence. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf otherLeft.graph) :=
  fun same => by
    have terms : normalWith 5 3 2 0 1 0 = normalWith 5 3 1 0 1 0 :=
      (denoteRanked_spelledTree_iff separable chain otherLeft).mp same
    simp at terms

example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf otherRight.graph) :=
  fun same => by
    have terms : normalWith 5 3 2 0 1 0 = normalWith 5 3 2 0 0 1 :=
      (denoteRanked_spelledTree_iff separable chain otherRight).mp same
    simp at terms

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain otherLeft) := fun holds =>
  left_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf otherLeft.graph) (spelled_graph chain) (spelled_graph otherLeft)).mpr holds)

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain otherRight) := fun holds =>
  right_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf otherRight.graph) (spelled_graph chain) (spelled_graph otherRight)).mpr holds)

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain otherArg) := fun holds =>
  arg_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf otherArg.graph) (spelled_graph chain) (spelled_graph otherArg)).mpr holds)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
