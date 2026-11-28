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

/-! ## Three tuples packed at once

There is one atom. `both` and `duo` take one atom and reply with a pair of
atoms. `ping` takes one atom and replies with one atom. `join` takes a pair
of atoms and replies with one atom. `pick` takes one atom and replies with
one of two tags: the first carries a pair of atoms and the second one atom.
Two older atoms are captured. The exits are a pair of atoms and one atom. -/

private inductive Op | both | duo | ping | join | pick

local instance : TaggedSignature Unit Op where
  argument
    | .both => .atom ()
    | .duo => .atom ()
    | .ping => .atom ()
    | .join => .pair (.atom ()) (.atom ())
    | .pick => .atom ()
  first
    | .both => [(), ()]
    | .duo => [(), ()]
    | .ping => [()]
    | .join => [()]
    | .pick => [(), ()]
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

private abbrev earlier : Slot older tok := ⟨1, rfl⟩

/-! ## The chain

Ask `both` on the earlier capture and hold its pair, the oldest. Ask `duo`
on the later capture and keep its pair packed, the middle one. Ask `duo`
again and keep its pair packed, the newest. With all three packed, ask
`ping` on the earlier capture. Destructure the newest pair into `z₁` and
`z₂`, and ask `join` on a chosen one of them and the earlier capture. Then
destructure the middle pair into `y₁` and `y₂`, and the oldest into `a` and
`b`, and return a chosen pair. -/

/-- One, two and three pairs packed. -/
private abbrev under₁ : BoundCtx (Ty Unit) 3 := older.snoc pairTy
private abbrev under₂ : BoundCtx (Ty Unit) 4 := under₁.snoc pairTy
private abbrev under₃ : BoundCtx (Ty Unit) 5 := under₂.snoc pairTy
private abbrev later₁ : Slot under₁ tok := ⟨1, rfl⟩
private abbrev later₂ : Slot under₂ tok := ⟨2, rfl⟩
private abbrev earlier₃ : Slot under₃ tok := ⟨4, rfl⟩

/-- After `ping` and the destructuring of the newest pair: `z₂`, `z₁`, the
reply of `ping`, the three pairs and the two captures. -/
private abbrev newestOpen : BoundCtx (Ty Unit) 8 := (((under₃.snoc tok).snoc tok).snoc tok)
private abbrev newestSecond : Slot newestOpen tok := ⟨0, rfl⟩
private abbrev newestFirst : Slot newestOpen tok := ⟨1, rfl⟩
private abbrev earlierNewest : Slot newestOpen tok := ⟨7, rfl⟩

/-- The leaf: `b`, `a`, `y₂`, `y₁`, the reply `d` of `join`, `z₂`, `z₁`, the
reply of `ping`, the three pairs and the two captures. -/
private abbrev leafCtx : BoundCtx (Ty Unit) 13 :=
  (((((newestOpen.snoc tok).snoc tok).snoc tok).snoc tok).snoc tok)
private abbrev oldestB : Slot leafCtx tok := ⟨0, rfl⟩
private abbrev oldestA : Slot leafCtx tok := ⟨1, rfl⟩
private abbrev middleSecond : Slot leafCtx tok := ⟨2, rfl⟩
private abbrev middleFirst : Slot leafCtx tok := ⟨3, rfl⟩
private abbrev replyD : Slot leafCtx tok := ⟨4, rfl⟩

/-- The tree with a chosen first argument of `join` and a chosen returned
pair. -/
private def chainWith (joined : Slot newestOpen tok) (first second : Slot leafCtx tok) :
    Spelled older exits
      (.let₁ (.op Op.both (.bv 1))
        (.let₁ (.op Op.duo (.bv 1))
          (.let₁ (.op Op.duo (.bv 2))
            (.let₁ (.op Op.ping (.bv 4))
              (.let₂ (.bv 1)
                (.let₁ (.op Op.join (.pair (.bv joined.1) (.bv 7)))
                  (.let₂ (.bv 5)
                    (.let₂ (.bv 8) (.inl (.pair (.bv first.1) (.bv second.1)))))))))) : Term 2) :=
  .ask Op.both (.atom earlier)
    (.bind (.only [(), ()]
      (.hold [(), ()]
        (.ask Op.duo (.atom later₁)
          (.bind [(), ()]
            (.ask Op.duo (.atom later₂)
              (.bind [(), ()]
                (.ask Op.ping (.atom earlier₃)
                  (.bind [()]
                    (.atom
                      (.step
                        (.atom
                          (.ask Op.join (.pair (.atom joined) (.atom earlierNewest))
                            (.bind [()]
                              (.atom
                                (.step
                                  (.atom
                                    (.step
                                      (.atom
                                        (.done (.ret pairExit (.pair (.atom first) (.atom second)))))))))))))))))))))))

/-- The normal form with a chosen first argument of `join` and a chosen
returned pair. Each pair is destructured right after the request that
binds it. The five requests keep their order. -/
private abbrev normalWith (joined : Fin 12) (first second : Fin 13) : Term 2 :=
  .let₁ (.op Op.both (.bv 1))
    (.let₂ (.bv 0)
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.duo (.bv 6))
            (.let₂ (.bv 0)
              (.let₁ (.op Op.ping (.bv 10))
                (.let₁ (.op Op.join (.pair (.bv joined) (.bv 11)))
                  (.inl (.pair (.bv first) (.bv second))))))))))

/-- `join` takes the first atom of the newest pair. The leaf returns the
first component of the oldest pair with the second component of the middle
pair. So the tree uses a component of each of the three pairs. -/
private abbrev chain := chainWith newestFirst oldestA middleSecond

/-- The spelled term. `ping` is asked while three pairs are packed. -/
example : Spelled older exits
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.duo (.bv 1))
        (.let₁ (.op Op.duo (.bv 2))
          (.let₁ (.op Op.ping (.bv 4))
            (.let₂ (.bv 1)
              (.let₁ (.op Op.join (.pair (.bv 1) (.bv 7)))
                (.let₂ (.bv 5)
                  (.let₂ (.bv 8) (.inl (.pair (.bv 1) (.bv 2)))))))))) : Term 2) := chain

/-- Its normal form. -/
private theorem chain_normal : (chain.normal (.id older)).1 = normalWith 2 9 5 := rfl

/-- The native equation between the spelling and its normal form. -/
example : Equiv false Γ₀ older
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.duo (.bv 1))
        (.let₁ (.op Op.duo (.bv 2))
          (.let₁ (.op Op.ping (.bv 4))
            (.let₂ (.bv 1)
              (.let₁ (.op Op.join (.pair (.bv 1) (.bv 7)))
                (.let₂ (.bv 5)
                  (.let₂ (.bv 8) (.inl (.pair (.bv 1) (.bv 2)))))))))) : Term 2)
    (normalWith 2 9 5) (packedExitType exits) :=
  spelled_equiv_normal chain

/-- In a larger context the normal form is the renamed normal form. -/
example : (chain.normal (BoundCtx.Renaming.succ older tok)).1 =
    (normalWith 2 9 5).rename Fin.succ :=
  spelled_normal_rename_term chain (.id older) (BoundCtx.Renaming.succ older tok)

/-! ## Variants -/

/-- The other component of the oldest pair is returned. -/
private abbrev otherOldest := chainWith newestFirst oldestB middleSecond

/-- The other component of the middle pair is returned. -/
private abbrev otherMiddle := chainWith newestFirst oldestA middleFirst

/-- `join` takes the other component of the newest pair. -/
private abbrev otherNewest := chainWith newestSecond oldestA middleSecond

/-- The reply of `join` is returned in place of a component of the middle
pair. -/
private abbrev replyReturned := chainWith newestFirst oldestA replyD

/-- The two returned atoms are exchanged. -/
private abbrev otherOrder := chainWith newestFirst middleSecond oldestA

example : (otherOldest.normal (.id older)).1 = normalWith 2 8 5 := rfl
example : (otherMiddle.normal (.id older)).1 = normalWith 2 9 6 := rfl
example : (otherNewest.normal (.id older)).1 = normalWith 1 9 5 := rfl
example : (replyReturned.normal (.id older)).1 = normalWith 2 9 0 := rfl
example : (otherOrder.normal (.id older)).1 = normalWith 2 5 9 := rfl

/-- The contexts of the eager spelling. -/
private abbrev opened₁ : BoundCtx (Ty Unit) 5 := ((older.snoc pairTy).snoc tok).snoc tok
private abbrev opened₂ : BoundCtx (Ty Unit) 8 := ((opened₁.snoc pairTy).snoc tok).snoc tok
private abbrev opened₃ : BoundCtx (Ty Unit) 11 := ((opened₂.snoc pairTy).snoc tok).snoc tok
private abbrev openedPing : BoundCtx (Ty Unit) 12 := opened₃.snoc tok
private abbrev openedJoin : BoundCtx (Ty Unit) 13 := openedPing.snoc tok

private def eagerLeaf :=
  Spelled.ret (Φ := Op) (β := openedJoin) pairExit (.pair (.atom ⟨9, rfl⟩) (.atom ⟨5, rfl⟩))

private def eagerJoin :=
  Spelled.ask Op.join (.pair (.atom (β := openedPing) ⟨2, rfl⟩) (.atom ⟨11, rfl⟩))
    (.bind (.only [()] (.atom () eagerLeaf)))

private def eagerPing :=
  Spelled.ask Op.ping (.atom (β := opened₃) ⟨10, rfl⟩) (.bind (.only [()] (.atom () eagerJoin)))

private def eagerNewest :=
  Spelled.ask Op.duo (.atom (β := opened₂) ⟨6, rfl⟩)
    (.bind (.only [(), ()] (.pair () () [] (.atom () eagerPing))))

private def eagerMiddle :=
  Spelled.ask Op.duo (.atom (β := opened₁) ⟨3, rfl⟩)
    (.bind (.only [(), ()] (.pair () () [] (.atom () eagerNewest))))

/-- The eager spelling: each pair is destructured as soon as it is bound.
It is the normal form of the chain. -/
private def eager : Spelled older exits (normalWith 2 9 5) :=
  .ask Op.both (.atom earlier) (.bind (.only [(), ()] (.pair () () [] (.atom () eagerMiddle))))

private theorem eager_normal : (eager.normal (.id older)).1 = normalWith 2 9 5 := rfl

/-! ## The payload of an arm kept packed

Ask `both` and hold its pair. Ask `pick` and case on its reply. Under the
first tag the pair payload is kept packed across `ping`, asked on the
earlier capture, and is then destructured; the held pair is destructured
after it, and the first atom of the payload is returned with the first
component of the held pair. Under the second tag the held pair is
destructured and its second component is returned with the payload. In the
first arm two tuples are packed across `ping`, and one of them is the
payload of an arm. -/

private abbrev underPick : BoundCtx (Ty Unit) 4 := under₁.snoc sumTy
private abbrev firstArm : BoundCtx (Ty Unit) 5 := underPick.snoc pairTy
private abbrev firstLeaf : BoundCtx (Ty Unit) 10 :=
  ((((firstArm.snoc tok).snoc tok).snoc tok).snoc tok).snoc tok
private abbrev secondLeaf : BoundCtx (Ty Unit) 7 := ((underPick.snoc tok).snoc tok).snoc tok

private def armKept : Spelled older exits
    (.let₁ (.op Op.both (.bv 1))
      (.let₁ (.op Op.pick (.bv 1))
        (.case (.bv 0)
          (.let₁ (.op Op.ping (.bv 4))
            (.let₂ (.bv 1) (.let₂ (.bv 5) (.inl (.pair (.bv 3) (.bv 1))))))
          (.let₂ (.bv 2) (.inl (.pair (.bv 0) (.bv 2)))))) : Term 2) :=
  .ask Op.both (.atom earlier)
    (.bind
      (.only [(), ()]
        (.hold [(), ()]
          (.ask Op.pick (.atom later₁)
            (.split [(), ()] [()] []
              (.ask Op.ping (.atom (β := firstArm) ⟨4, rfl⟩)
                (.bind [()]
                  (.atom
                    (.step
                      (.atom
                        (.step
                          (.atom
                            (.done
                              (.ret pairExit (.pair (.atom (β := firstLeaf) ⟨3, rfl⟩) (.atom ⟨1, rfl⟩)))))))))))
              (.bind [()]
                (.atom
                  (.step
                    (.atom
                      (.done
                        (.ret pairExit (.pair (.atom (β := secondLeaf) ⟨0, rfl⟩) (.atom ⟨2, rfl⟩)))))))))))))

/-- The held pair is destructured before `pick`. The case is still on the
reply of `pick` and directly follows it. The payload of the first tag is
destructured at the start of its arm, before `ping`. -/
example : (armKept.normal (.id older)).1 =
    (.let₁ (.op Op.both (.bv 1))
      (.let₂ (.bv 0)
        (.let₁ (.op Op.pick (.bv 3))
          (.case (.bv 0)
            (.let₂ (.bv 0) (.let₁ (.op Op.ping (.bv 8)) (.inl (.pair (.bv 2) (.bv 6)))))
            (.inl (.pair (.bv 2) (.bv 0)))))) : Term 2) := rfl

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

/-- Which component of the oldest pair is returned. -/
private theorem oldest_apart : ¬ RankedValid false (sentence chain otherOldest) := fun valid => by
  have same : normalWith 2 9 5 = normalWith 2 8 5 :=
    (rankedValid_spelledTree_iff separable chain otherOldest).mp valid
  simp at same

/-- Which component of the middle pair is returned. -/
private theorem middle_apart : ¬ RankedValid false (sentence chain otherMiddle) := fun valid => by
  have same : normalWith 2 9 5 = normalWith 2 9 6 :=
    (rankedValid_spelledTree_iff separable chain otherMiddle).mp valid
  simp at same

/-- Which component of the newest pair the following request takes. -/
private theorem newest_apart : ¬ RankedValid false (sentence chain otherNewest) := fun valid => by
  have same : normalWith 2 9 5 = normalWith 1 9 5 :=
    (rankedValid_spelledTree_iff separable chain otherNewest).mp valid
  simp at same

/-- A component of the middle pair and the reply of the following request. -/
example : ¬ RankedValid false (sentence chain replyReturned) := fun valid => by
  have same : normalWith 2 9 5 = normalWith 2 9 0 :=
    (rankedValid_spelledTree_iff separable chain replyReturned).mp valid
  simp at same

/-- The oldest and the middle pair are told apart: exchanging the returned
components. -/
example : ¬ RankedValid false (sentence chain otherOrder) := fun valid => by
  have same : normalWith 2 9 5 = normalWith 2 5 9 :=
    (rankedValid_spelledTree_iff separable chain otherOrder).mp valid
  simp at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms,
and the model rejects each sentence. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf otherOldest.graph) :=
  fun same => by
    have terms : normalWith 2 9 5 = normalWith 2 8 5 :=
      (denoteRanked_spelledTree_iff separable chain otherOldest).mp same
    simp at terms

example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf otherMiddle.graph) :=
  fun same => by
    have terms : normalWith 2 9 5 = normalWith 2 9 6 :=
      (denoteRanked_spelledTree_iff separable chain otherMiddle).mp same
    simp at terms

example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf chain.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf otherNewest.graph) :=
  fun same => by
    have terms : normalWith 2 9 5 = normalWith 1 9 5 :=
      (denoteRanked_spelledTree_iff separable chain otherNewest).mp same
    simp at terms

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain otherOldest) := fun holds =>
  oldest_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf otherOldest.graph) (spelled_graph chain) (spelled_graph otherOldest)).mpr holds)

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain otherMiddle) := fun holds =>
  middle_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf otherMiddle.graph) (spelled_graph chain) (spelled_graph otherMiddle)).mpr holds)

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence chain otherNewest) := fun holds =>
  newest_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf chain.graph)
    (entryOf otherNewest.graph) (spelled_graph chain) (spelled_graph otherNewest)).mpr holds)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
