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

/-! ## Opening the oldest of three packed tuples

There is one atom. `both` and `duo` take one atom and reply with a pair of
atoms. `join` takes a pair of atoms and replies with one atom. Every reply
has one tag. Two older atoms are captured. The exits are a pair of atoms
and one atom. -/

private inductive Op | both | duo | join

local instance : TaggedSignature Unit Op where
  argument
    | .both => .atom ()
    | .duo => .atom ()
    | .join => .pair (.atom ()) (.atom ())
  first
    | .both => [(), ()]
    | .duo => [(), ()]
    | .join => [()]
  others _ := []

private abbrev tok : Ty Unit := .base ()
private abbrev pairTy : Ty Unit := .product tok tok
private abbrev older : BoundCtx (Ty Unit) 2 := (BoundCtx.snoc .nil tok).snoc tok
private abbrev Term (n : Nat) := LetCase.LocallyNameless.Tm Empty Op n

private theorem separable : Separable older := separable_atoms (.snoc (.snoc .nil ()) ())

private abbrev exits : List (Ty Unit) := [pairTy, tok]
private abbrev pairExit : ExitAt exits pairTy := .here

private abbrev earlier : Slot older tok := ⟨1, rfl⟩

/-! ## The chain

Ask `both` on the earlier capture and hold its pair, the oldest. Ask `duo`
on the later capture and keep its pair packed, the middle one. Ask `duo`
again and keep its pair packed, the newest. With all three packed, select
the oldest pair and destructure it into `a` and `b`. The middle and the
newest pair stay packed. Ask `join` on a chosen atom and the earlier
capture, with reply `d`. Then destructure the newest pair into `z₁` and
`z₂`, and the middle pair into `y₁` and `y₂`, and return a chosen pair. -/

/-- One, two and three pairs packed. -/
private abbrev under₁ : BoundCtx (Ty Unit) 3 := older.snoc pairTy
private abbrev under₂ : BoundCtx (Ty Unit) 4 := under₁.snoc pairTy
private abbrev under₃ : BoundCtx (Ty Unit) 5 := under₂.snoc pairTy
private abbrev later₁ : Slot under₁ tok := ⟨1, rfl⟩
private abbrev later₂ : Slot under₂ tok := ⟨2, rfl⟩

/-- After the oldest pair is destructured: `b`, `a`, the three pairs and
the two captures. The newest and the middle pair are still packed. -/
private abbrev oldestOpen : BoundCtx (Ty Unit) 7 := (under₃.snoc tok).snoc tok
private abbrev oldestB : Slot oldestOpen tok := ⟨0, rfl⟩
private abbrev oldestA : Slot oldestOpen tok := ⟨1, rfl⟩
private abbrev laterOpen : Slot oldestOpen tok := ⟨5, rfl⟩
private abbrev earlierOpen : Slot oldestOpen tok := ⟨6, rfl⟩

/-- The leaf, with the newest pair destructured before the middle one:
`y₂`, `y₁`, `z₂`, `z₁`, `d`, `b`, `a`, the three pairs and the two
captures. -/
private abbrev leafCtx : BoundCtx (Ty Unit) 12 :=
  ((((oldestOpen.snoc tok).snoc tok).snoc tok).snoc tok).snoc tok
private abbrev middleSecond : Slot leafCtx tok := ⟨0, rfl⟩
private abbrev middleFirst : Slot leafCtx tok := ⟨1, rfl⟩
private abbrev newestSecond : Slot leafCtx tok := ⟨2, rfl⟩
private abbrev newestFirst : Slot leafCtx tok := ⟨3, rfl⟩
private abbrev leafB : Slot leafCtx tok := ⟨5, rfl⟩

/-- The tree with a chosen first argument of `join` and a chosen returned
pair. The selection `there (there here)` names the oldest of the three
packed pairs. -/
private def chainWith (joined : Slot oldestOpen tok) (first second : Slot leafCtx tok) :
    Spelled older exits
      (.let₁ (.op Op.both (.bv 1))
        (.let₁ (.op Op.duo (.bv 1))
          (.let₁ (.op Op.duo (.bv 2))
            (.let₂ (.bv 2)
              (.let₁ (.op Op.join (.pair (.bv joined.1) (.bv 6)))
                (.let₂ (.bv 3)
                  (.let₂ (.bv 6) (.inl (.pair (.bv first.1) (.bv second.1))))))))) : Term 2) :=
  .ask Op.both (.atom earlier)
    (.bind
      (.only [(), ()]
        (.hold [(), ()]
          (.ask Op.duo (.atom later₁)
            (.bind [(), ()]
              (.ask Op.duo (.atom later₂)
                (.bind [(), ()]
                  (.pick (.there (.there .here))
                    (.step
                      (.atom
                        (.ask Op.join (.pair (.atom joined) (.atom earlierOpen))
                          (.bind [()]
                            (.atom
                              (.step
                                (.atom
                                  (.step
                                    (.atom
                                      (.done (.ret pairExit (.pair (.atom first) (.atom second)))))))))))))))))))))

/-- The normal form with a chosen first argument of `join` and a chosen
returned pair. Each pair is destructured right after the request that
binds it. The four requests keep their order. -/
private abbrev normalWith (joined : Fin 11) (first second : Fin 12) : Term 2 :=
  .let₁ (.op Op.both (.bv 1))
    (.let₂ (.bv 0)
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.duo (.bv 6))
            (.let₂ (.bv 0)
              (.let₁ (.op Op.join (.pair (.bv joined) (.bv 10)))
                (.inl (.pair (.bv first) (.bv second)))))))))

/-- `join` takes the first component of the oldest pair, just opened, and
the earlier capture. The leaf returns the first component of the newest
pair with the second component of the middle pair. -/
private abbrev chain := chainWith oldestA newestFirst middleSecond

/-- The spelled term. The oldest pair is destructured by `let₂ (bv 2)`
while the two newer pairs, at slots 0 and 1, stay packed across `join`. -/
example : Spelled older exits
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.duo (.bv 1))
        (.let₁ (.op Op.duo (.bv 2))
          (.let₂ (.bv 2)
            (.let₁ (.op Op.join (.pair (.bv 1) (.bv 6)))
              (.let₂ (.bv 3)
                (.let₂ (.bv 6) (.inl (.pair (.bv 3) (.bv 0))))))))) : Term 2) := chain

/-- Its normal form. -/
private theorem chain_normal : (chain.normal (.id older)).1 = normalWith 7 2 4 := rfl

/-- The native equation between the spelling and its normal form. -/
example : Equiv false Γ₀ older
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.duo (.bv 1))
        (.let₁ (.op Op.duo (.bv 2))
          (.let₂ (.bv 2)
            (.let₁ (.op Op.join (.pair (.bv 1) (.bv 6)))
              (.let₂ (.bv 3)
                (.let₂ (.bv 6) (.inl (.pair (.bv 3) (.bv 0))))))))) : Term 2)
    (normalWith 7 2 4) (packedExitType exits) :=
  spelled_equiv_normal chain

/-- In a larger context the normal form is the renamed normal form. -/
example : (chain.normal (BoundCtx.Renaming.succ older tok)).1 =
    (normalWith 7 2 4).rename Fin.succ :=
  spelled_normal_rename_term chain (.id older) (BoundCtx.Renaming.succ older tok)

/-! ## Variants -/

/-- `join` takes the other component of the oldest pair. -/
private abbrev otherOpened := chainWith oldestB newestFirst middleSecond

/-- `join` takes the later capture in place of the opened component. -/
private abbrev captureJoined := chainWith laterOpen newestFirst middleSecond

/-- The other component of the newest pair is returned. -/
private abbrev otherNewest := chainWith oldestA newestSecond middleSecond

/-- The other component of the middle pair is returned. -/
private abbrev otherMiddle := chainWith oldestA newestFirst middleFirst

/-- A component of the oldest pair is returned in place of one of the
middle pair. -/
private abbrev oldestReturned := chainWith oldestA newestFirst leafB

/-- The two returned atoms are exchanged. -/
private abbrev otherOrder := chainWith oldestA middleSecond newestFirst

example : (otherOpened.normal (.id older)).1 = normalWith 6 2 4 := rfl
example : (captureJoined.normal (.id older)).1 = normalWith 9 2 4 := rfl
example : (otherNewest.normal (.id older)).1 = normalWith 7 1 4 := rfl
example : (otherMiddle.normal (.id older)).1 = normalWith 7 2 5 := rfl
example : (oldestReturned.normal (.id older)).1 = normalWith 7 2 7 := rfl
example : (otherOrder.normal (.id older)).1 = normalWith 7 4 2 := rfl

/-- The contexts of the eager spelling. -/
private abbrev opened₁ : BoundCtx (Ty Unit) 5 := ((older.snoc pairTy).snoc tok).snoc tok
private abbrev opened₂ : BoundCtx (Ty Unit) 8 := ((opened₁.snoc pairTy).snoc tok).snoc tok
private abbrev opened₃ : BoundCtx (Ty Unit) 11 := ((opened₂.snoc pairTy).snoc tok).snoc tok
private abbrev openedJoin : BoundCtx (Ty Unit) 12 := opened₃.snoc tok

private def eagerLeaf :=
  Spelled.ret (Φ := Op) (β := openedJoin) pairExit (.pair (.atom ⟨2, rfl⟩) (.atom ⟨4, rfl⟩))

private def eagerJoin :=
  Spelled.ask Op.join (.pair (.atom (β := opened₃) ⟨7, rfl⟩) (.atom ⟨10, rfl⟩))
    (.bind (.only [()] (.atom () eagerLeaf)))

private def eagerNewest :=
  Spelled.ask Op.duo (.atom (β := opened₂) ⟨6, rfl⟩)
    (.bind (.only [(), ()] (.pair () () [] (.atom () eagerJoin))))

private def eagerMiddle :=
  Spelled.ask Op.duo (.atom (β := opened₁) ⟨3, rfl⟩)
    (.bind (.only [(), ()] (.pair () () [] (.atom () eagerNewest))))

/-- The eager spelling: each pair is destructured as soon as it is bound.
It is the normal form of the chain. -/
private def eager : Spelled older exits (normalWith 7 2 4) :=
  .ask Op.both (.atom earlier) (.bind (.only [(), ()] (.pair () () [] (.atom () eagerMiddle))))

private theorem eager_normal : (eager.normal (.id older)).1 = normalWith 7 2 4 := rfl

/-! ## The middle pair opened before the newest

The same chain, but after `join` the middle pair is selected and
destructured before the newest one. The three pairs are opened oldest
first, the reverse of the order in which they were bound. The leaf returns
the same atoms, so the normal form is the same. -/

private def oldestFirst : Spelled older exits
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.duo (.bv 1))
        (.let₁ (.op Op.duo (.bv 2))
          (.let₂ (.bv 2)
            (.let₁ (.op Op.join (.pair (.bv 1) (.bv 6)))
              (.let₂ (.bv 4)
                (.let₂ (.bv 5) (.inl (.pair (.bv 1) (.bv 2))))))))) : Term 2) :=
  .ask Op.both (.atom earlier)
    (.bind
      (.only [(), ()]
        (.hold [(), ()]
          (.ask Op.duo (.atom later₁)
            (.bind [(), ()]
              (.ask Op.duo (.atom later₂)
                (.bind [(), ()]
                  (.pick (.there (.there .here))
                    (.step
                      (.atom
                        (.ask Op.join (.pair (.atom oldestA) (.atom earlierOpen))
                          (.bind [()]
                            (.atom
                              (.pick (.there .here)
                                (.step
                                  (.atom
                                    (.step
                                      (.atom
                                        (.done
                                          (.ret pairExit (.pair (.atom (β := leafCtx) ⟨1, rfl⟩) (.atom ⟨2, rfl⟩))))))))))))))))))))))

private theorem oldestFirst_normal : (oldestFirst.normal (.id older)).1 = normalWith 7 2 4 := rfl

/-! ## Ranked validity and ordered-exit arrows -/

private abbrev sentence {t u : Term 2} (p : Spelled older exits t) (q : Spelled older exits u) :
    RankedEquation (atomSig Unit Op) :=
  sentenceOf (entryOf p.graph) (entryOf q.graph)

/-- The chain and the eager spelling are one sentence. -/
private theorem chain_eager : RankedValid false (sentence chain eager) :=
  (rankedValid_spelledTree_iff separable chain eager).mpr (chain_normal.trans eager_normal.symm)

/-- They have the same ordered-exit arrow at the ordered trace model with
atoms. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) =
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf eager.graph) :=
  (denoteRanked_spelledTree_iff separable chain eager).mpr (chain_normal.trans eager_normal.symm)

/-- The two orders of opening the newer pairs are one sentence. -/
example : RankedValid false (sentence chain oldestFirst) :=
  (rankedValid_spelledTree_iff separable chain oldestFirst).mpr (chain_normal.trans oldestFirst_normal.symm)

/-- Which component of the opened pair the following request takes. -/
private theorem opened_apart : ¬ RankedValid false (sentence chain otherOpened) := fun valid => by
  have same : normalWith 7 2 4 = normalWith 6 2 4 :=
    (rankedValid_spelledTree_iff separable chain otherOpened).mp valid
  simp at same

/-- The opened component and an older capture, as the argument of the
following request. -/
private theorem capture_apart : ¬ RankedValid false (sentence chain captureJoined) := fun valid => by
  have same : normalWith 7 2 4 = normalWith 9 2 4 :=
    (rankedValid_spelledTree_iff separable chain captureJoined).mp valid
  simp at same

/-- Which component of the newest pair is returned. -/
example : ¬ RankedValid false (sentence chain otherNewest) := fun valid => by
  have same : normalWith 7 2 4 = normalWith 7 1 4 :=
    (rankedValid_spelledTree_iff separable chain otherNewest).mp valid
  simp at same

/-- Which component of the middle pair is returned. -/
example : ¬ RankedValid false (sentence chain otherMiddle) := fun valid => by
  have same : normalWith 7 2 4 = normalWith 7 2 5 :=
    (rankedValid_spelledTree_iff separable chain otherMiddle).mp valid
  simp at same

/-- A component of the middle pair and one of the oldest pair. -/
example : ¬ RankedValid false (sentence chain oldestReturned) := fun valid => by
  have same : normalWith 7 2 4 = normalWith 7 2 7 :=
    (rankedValid_spelledTree_iff separable chain oldestReturned).mp valid
  simp at same

/-- The newest and the middle pair are told apart: exchanging the returned
components. -/
example : ¬ RankedValid false (sentence chain otherOrder) := fun valid => by
  have same : normalWith 7 2 4 = normalWith 7 4 2 :=
    (rankedValid_spelledTree_iff separable chain otherOrder).mp valid
  simp at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms,
and the model rejects each sentence. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf otherOpened.graph) :=
  fun same => by
    have terms : normalWith 7 2 4 = normalWith 6 2 4 :=
      (denoteRanked_spelledTree_iff separable chain otherOpened).mp same
    simp at terms

example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf captureJoined.graph) :=
  fun same => by
    have terms : normalWith 7 2 4 = normalWith 9 2 4 :=
      (denoteRanked_spelledTree_iff separable chain captureJoined).mp same
    simp at terms

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain otherOpened) := fun holds =>
  opened_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf otherOpened.graph) (spelled_graph chain) (spelled_graph otherOpened)).mpr holds)

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain captureJoined) := fun holds =>
  capture_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf captureJoined.graph) (spelled_graph chain) (spelled_graph captureJoined)).mpr holds)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
