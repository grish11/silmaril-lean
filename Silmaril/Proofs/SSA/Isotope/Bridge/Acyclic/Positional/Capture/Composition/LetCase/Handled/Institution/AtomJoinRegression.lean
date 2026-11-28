module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Join.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation denoteRanked)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Slot Assembly)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
open scoped LetSeq.StraightLine.Structural Tagged

/-! ## A shared join before the stored reply is inspected

There is one atom. `pick` takes one atom and replies with one of two tags:
the first carries a pair of atoms and the second one atom. `test` takes
one atom and replies with one of two tags: the first carries one atom and
the second a pair of atoms. `echo` and `mark` take one atom and reply with
one atom. Two older atoms are captured. The exits are a pair of atoms and
one atom. -/

private inductive Op | pick | test | echo | mark
  deriving DecidableEq

local instance : TaggedSignature Unit Op where
  argument
    | .pick => .atom ()
    | .test => .atom ()
    | .echo => .atom ()
    | .mark => .atom ()
  first
    | .pick => [(), ()]
    | .test => [()]
    | .echo => [()]
    | .mark => [()]
  others
    | .pick => [[()]]
    | .test => [[(), ()]]
    | .echo => []
    | .mark => []

private abbrev tok : Ty Unit := .base ()
private abbrev pairTy : Ty Unit := .product tok tok
private abbrev sumTy : Ty Unit := .coprod pairTy tok
private abbrev testTy : Ty Unit := .coprod tok pairTy
private abbrev older : BoundCtx (Ty Unit) 2 := (BoundCtx.snoc .nil tok).snoc tok
private abbrev Term (n : Nat) := LetCase.LocallyNameless.Tm Empty Op n

private theorem separable : Separable older := separable_atoms (.snoc (.snoc .nil ()) ())

private abbrev exits : List (Ty Unit) := [pairTy, tok]
private abbrev pairExit : ExitAt exits pairTy := .here

private abbrev later : Slot older tok := ⟨0, rfl⟩

/-! ## The joined original

Ask `pick` on the later capture and bind its reply `s`, a slot of sum
type. While `s` is one slot, ask `test` on the earlier capture and case on
its reply. The two arms supply one atom to a common continuation.

Under the first tag of `test`, with payload `a`: ask `echo` on `a`, with
reply `e`, and supply `e`. This is the effect before the join. Under the
second tag, with payload a pair, destructure it into `b₁` and `b₂` and
supply `b₂`.

The continuation is written once. With the supplied atom `j`: ask `mark`
on `j`, with reply `f`; then case on `s`. Under the first tag of `s`, with
payload a pair, destructure it into `x₁` and `x₂` and return `x₁` with
`f`. Under the second tag, with payload `q`, return a chosen atom, `q` by
default, with `j`. -/

/-- Under the stored reply, and under the reply of `test`. -/
private abbrev underS : BoundCtx (Ty Unit) 3 := older.snoc sumTy
private abbrev underY : BoundCtx (Ty Unit) 4 := underS.snoc testTy

/-- The first arm: `a` and then `e`; the second arm: the payload and then
its two components. -/
private abbrev armA : BoundCtx (Ty Unit) 5 := underY.snoc tok
private abbrev armAe : BoundCtx (Ty Unit) 6 := armA.snoc tok
private abbrev armB : BoundCtx (Ty Unit) 5 := underY.snoc pairTy
private abbrev armBb : BoundCtx (Ty Unit) 7 := (armB.snoc tok).snoc tok

/-- The continuation: the joined atom `j`, then `f`, and the leaves. -/
private abbrev joined : BoundCtx (Ty Unit) 5 := underY.snoc tok
private abbrev afterMark : BoundCtx (Ty Unit) 6 := joined.snoc tok
private abbrev leafL : BoundCtx (Ty Unit) 9 := ((afterMark.snoc pairTy).snoc tok).snoc tok
private abbrev leafR : BoundCtx (Ty Unit) 7 := afterMark.snoc tok

/-- The first arm supplies the reply of `echo`: `echo` is asked, the
payload `a` is selected and dropped, and `e` is left on top of the
stack. -/
private def leftReply : SpelledPrefix (Φ := Op) [[()]] armA (.cons ⟨0, rfl⟩ .nil) [[()]] armAe
    (.cons ⟨0, rfl⟩ .nil) :=
  .ask Op.echo (.atom (β := armA) ⟨0, rfl⟩) (.bind [()] (.pick (.there .here) (.atom .stop)))

/-- The first arm supplies its payload `a` instead: `echo` is still asked,
its reply is dropped, and `a` is left on top of the stack. -/
private def leftPayload : SpelledPrefix (Φ := Op) [[()]] armA (.cons ⟨0, rfl⟩ .nil) [[()]] armAe
    (.cons ⟨1, rfl⟩ .nil) :=
  .ask Op.echo (.atom (β := armA) ⟨0, rfl⟩) (.bind [()] (.atom .stop))

/-- The second arm supplies the second component of its payload. -/
private def rightArm : SpelledPrefix (Φ := Op) [[(), ()]] armB (.cons ⟨0, rfl⟩ .nil) [[()]] armBb
    (.cons ⟨0, rfl⟩ .nil) :=
  .step .stop

/-- The arms of `s` in the continuation. -/
private def firstArm : SpelledStack (Φ := Op) [[(), ()]] (afterMark.snoc pairTy) (.cons ⟨0, rfl⟩ .nil) exits
    (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))) : Term 7) :=
  .step (.atom (.done (.ret pairExit (.pair (.atom (β := leafL) ⟨1, rfl⟩) (.atom ⟨3, rfl⟩)))))

private def secondArm (component : Slot leafR tok) : SpelledStack (Φ := Op) [[()]] leafR
    (.cons ⟨0, rfl⟩ .nil) exits (.inl (.pair (.bv component.1) (.bv 2)) : Term 7) :=
  .atom (.done (.ret pairExit (.pair (.atom (β := leafR) component) (.atom ⟨2, rfl⟩))))

/-- The continuation, written once: `mark` on the joined atom, then the
case on `s`. -/
private def continuation (component : Slot leafR tok) :
    SpelledDelay (Φ := Op) [(), ()] [()] [[()]] joined (.cons ⟨0, rfl⟩ .nil) 2 exits
      (.let₁ (.op Op.mark (.bv 0))
        (.case (.bv 3)
          (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
          (.inl (.pair (.bv component.1) (.bv 2)))) : Term 5) :=
  .atom
    (.ask Op.mark (.atom (β := joined) ⟨0, rfl⟩)
      (.bind [()] (.atom (.inspect (Δ := afterMark) ⟨3, rfl⟩ firstArm (secondArm component)))))

/-- The join, with the first arm supplying the reply of `echo`. Its term
is a let whose bound term is the case on the reply of `test`. -/
private def join (component : Slot leafR tok) :
    SpelledJoinTags (Φ := Op) [(), ()] [()] [] [[()], [(), ()]] underS .nil 0 exits
      (.let₁ (.case (.bv 0) (.let₁ (.op Op.echo (.bv 0)) (.bv 0)) (.let₂ (.bv 0) (.bv 0)))
        (.let₁ (.op Op.mark (.bv 0))
          (.case (.bv 3)
            (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
            (.inl (.pair (.bv component.1) (.bv 2))))) : Term 4) :=
  (SpelledJoinTags.join (atoms := [(), ()]) (next := [()]) (stack := []) (Δ := underS) (holds := .nil)
    (s := 0) (L := exits) [()] [(), ()] [()] leftReply rfl rightArm rfl (continuation component) :
    SpelledJoinTags (Φ := Op) [(), ()] [()] [] [[()], [(), ()]] underS .nil 0 exits _)

/-- The join with the first arm supplying its payload. The supplied slot
is the only change in the term. -/
private def joinPayload :
    SpelledJoinTags (Φ := Op) [(), ()] [()] [] [[()], [(), ()]] underS .nil 0 exits
      (.let₁ (.case (.bv 0) (.let₁ (.op Op.echo (.bv 0)) (.bv 1)) (.let₂ (.bv 0) (.bv 0)))
        (.let₁ (.op Op.mark (.bv 0))
          (.case (.bv 3)
            (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
            (.inl (.pair (.bv 0) (.bv 2))))) : Term 4) :=
  (SpelledJoinTags.join (atoms := [(), ()]) (next := [()]) (stack := []) (Δ := underS) (holds := .nil)
    (s := 0) (L := exits) [()] [(), ()] [()] leftPayload rfl rightArm rfl (continuation ⟨0, rfl⟩) :
    SpelledJoinTags (Φ := Op) [(), ()] [()] [] [[()], [(), ()]] underS .nil 0 exits _)

/-- The whole term around a term under the reply of `test`. -/
private abbrev around (t : Term 4) : Term 2 :=
  .let₁ (.op Op.pick (.bv 0)) (.let₁ (.op Op.test (.bv 2)) t)

/-- The native typing of the joined original, at the packed exits. -/
private def joinedTyping {t : Term 4}
    (j : SpelledJoinTags (Φ := Op) [(), ()] [()] [] [[()], [(), ()]] underS .nil 0 exits t) :
    Derivation Op Γ₀ older (around t) (packedExitType exits) :=
  .let₁ (.op (f := Op.pick) (argTyping (Assembly.atom later)))
    (.let₁ (.op (f := Op.test) (argTyping (Assembly.atom (β := underS) ⟨2, rfl⟩))) j.typing)

/-- The expansion: the stored reply above the reply of `test`, cased on at
once, with the continuation in each arm. It is a tree of the grammar. -/
private def expanded {t : Term 4}
    (j : SpelledJoinTags (Φ := Op) [(), ()] [()] [] [[()], [(), ()]] underS .nil 0 exits t) :
    Spelled older exits (around j.expand.term) :=
  .chain (.ask Op.pick (.atom later)
    (SpelledStackTags.delayedTree (stack := []) (Δ := older) (holds := .nil) [(), ()] [()]
      (.ask Op.test (.atom (β := underS) ⟨2, rfl⟩) j.expand.tree)))

/-- The joined original is natively equal to its expansion. The join is
inlined under the two requests. -/
private theorem joined_native {t : Term 4}
    (j : SpelledJoinTags (Φ := Op) [(), ()] [()] [] [[()], [(), ()]] underS .nil 0 exits t) :
    Equiv false Γ₀ older (around t) (around j.expand.term) (packedExitType exits) :=
  Equiv.let₁ (.refl (Derivation.op (f := Op.pick) (argTyping (Assembly.atom later))).toHasType)
    (Equiv.let₁
      (.refl (Derivation.op (f := Op.test) (argTyping (Assembly.atom (β := underS) ⟨2, rfl⟩))).toHasType)
      (spelledJoinTags_equiv_expand j))

/-- The term of the expansion: the continuation is in both arms, with the
joined atom replaced by the reply of `echo` in the first and by the
component of the payload in the second. `echo` comes before `mark` on the
first path, as in the join. -/
example : around (join ⟨0, rfl⟩).expand.term =
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.test (.bv 2))
        (.case (.bv 0)
          (.let₁ (.op Op.echo (.bv 0))
            (.let₁ (.op Op.mark (.bv 0))
              (.case (.bv 4)
                (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
                (.inl (.pair (.bv 0) (.bv 2))))))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.mark (.bv 0))
              (.case (.bv 5)
                (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
                (.inl (.pair (.bv 0) (.bv 2)))))))) : Term 2) := by
  decide +kernel

/-- The normal form with the chosen arguments of `mark` under the first
tag of `test` and the chosen returned atoms under the second tag of `s`.
On every path the requests are in the order of the joined original:
`pick`, `test`, then `echo` under the first tag of `test`, then `mark`. -/
private abbrev normalWith (markL : Fin 9) (markR : Fin 7) (suppliedR qA : Fin 8) (qB : Fin 9) : Term 2 :=
  .let₁ (.op Op.pick (.bv 0))
    (.case (.bv 0)
      (.let₂ (.bv 0)
        (.let₁ (.op Op.test (.bv 5))
          (.case (.bv 0)
            (.let₁ (.op Op.echo (.bv 0)) (.let₁ (.op Op.mark (.bv markL)) (.inl (.pair (.bv 5) (.bv 0)))))
            (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 0)) (.inl (.pair (.bv 6) (.bv 0))))))))
      (.let₁ (.op Op.test (.bv 3))
        (.case (.bv 0)
          (.let₁ (.op Op.echo (.bv 0))
            (.let₁ (.op Op.mark (.bv markR)) (.inl (.pair (.bv qA) (.bv suppliedR)))))
          (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 0)) (.inl (.pair (.bv qB) (.bv 1))))))))

private theorem expanded_normal :
    ((expanded (join ⟨0, rfl⟩)).normal (.id older)).1 = normalWith 0 0 1 4 5 := by decide +kernel


/-- The joined original is natively equal to the normal form of its
expansion. -/
private theorem joined_normal_native : Equiv false Γ₀ older
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.test (.bv 2))
        (.let₁ (.case (.bv 0) (.let₁ (.op Op.echo (.bv 0)) (.bv 0)) (.let₂ (.bv 0) (.bv 0)))
          (.let₁ (.op Op.mark (.bv 0))
            (.case (.bv 3)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2))))))) : Term 2)
    (normalWith 0 0 1 4 5) (packedExitType exits) :=
  (joined_native (join ⟨0, rfl⟩)).trans (expanded_normal ▸ spelled_equiv_normal (expanded (join ⟨0, rfl⟩)))

/-! ## The eager spelling

The reply of `pick` is cased on at once. Each of its arms is written by
hand as a tree: `test` is asked and cased on with the payload of `s`
packed, the first arm of `test` asks `echo` and then `mark` on its reply,
the second destructures its payload and asks `mark` on a component, and
then the payload of `s` is opened. There is no join: the continuation is
written in each of the four leaves. -/

private abbrev eagerP : BoundCtx (Ty Unit) 4 := underS.snoc pairTy
private abbrev eagerPA : BoundCtx (Ty Unit) 6 := (eagerP.snoc testTy).snoc tok
private abbrev eagerPAe : BoundCtx (Ty Unit) 7 := eagerPA.snoc tok
private abbrev eagerPAleaf : BoundCtx (Ty Unit) 10 := ((eagerPAe.snoc tok).snoc tok).snoc tok
private abbrev eagerPB : BoundCtx (Ty Unit) 8 := (((eagerP.snoc testTy).snoc pairTy).snoc tok).snoc tok
private abbrev eagerPBleaf : BoundCtx (Ty Unit) 11 := ((eagerPB.snoc tok).snoc tok).snoc tok
private abbrev eagerQ : BoundCtx (Ty Unit) 4 := underS.snoc tok
private abbrev eagerQA : BoundCtx (Ty Unit) 6 := (eagerQ.snoc testTy).snoc tok
private abbrev eagerQAe : BoundCtx (Ty Unit) 7 := eagerQA.snoc tok
private abbrev eagerQAleaf : BoundCtx (Ty Unit) 8 := eagerQAe.snoc tok
private abbrev eagerQB : BoundCtx (Ty Unit) 8 := (((eagerQ.snoc testTy).snoc pairTy).snoc tok).snoc tok
private abbrev eagerQBleaf : BoundCtx (Ty Unit) 9 := eagerQB.snoc tok

/-- The arm of the first tag of `s`. -/
private def eagerFirst :=
  SpelledStack.ask (L := exits) (stack := [[(), ()]]) (Δ := eagerP) (holds := .cons ⟨0, rfl⟩ .nil) Op.test
    (.atom (β := eagerP) ⟨3, rfl⟩)
    (.split [()] [(), ()] []
      (.atom
        (.ask Op.echo (.atom (β := eagerPA) ⟨0, rfl⟩)
          (.bind [()]
            (.atom
              (.ask Op.mark (.atom (β := eagerPAe) ⟨0, rfl⟩)
                (.bind [()]
                  (.atom
                    (.step
                      (.atom
                        (.done (.ret pairExit (.pair (.atom (β := eagerPAleaf) ⟨1, rfl⟩) (.atom ⟨2, rfl⟩)))))))))))))
      (.bind [(), ()]
        (.step
          (.atom
            (.ask Op.mark (.atom (β := eagerPB) ⟨0, rfl⟩)
              (.bind [()]
                (.atom
                  (.step
                    (.atom
                      (.done (.ret pairExit (.pair (.atom (β := eagerPBleaf) ⟨1, rfl⟩) (.atom ⟨2, rfl⟩)))))))))))))

/-- The arm of the second tag of `s`. -/
private def eagerSecond :=
  SpelledStack.ask (L := exits) (stack := [[()]]) (Δ := eagerQ) (holds := .cons ⟨0, rfl⟩ .nil) Op.test
    (.atom (β := eagerQ) ⟨3, rfl⟩)
    (.split [()] [(), ()] []
      (.atom
        (.ask Op.echo (.atom (β := eagerQA) ⟨0, rfl⟩)
          (.bind [()]
            (.atom
              (.ask Op.mark (.atom (β := eagerQAe) ⟨0, rfl⟩)
                (.bind [()]
                  (.atom
                    (.atom
                      (.done (.ret pairExit (.pair (.atom (β := eagerQAleaf) ⟨4, rfl⟩) (.atom ⟨1, rfl⟩))))))))))))
      (.bind [(), ()]
        (.step
          (.atom
            (.ask Op.mark (.atom (β := eagerQB) ⟨0, rfl⟩)
              (.bind [()]
                (.atom
                  (.atom
                    (.done (.ret pairExit (.pair (.atom (β := eagerQBleaf) ⟨5, rfl⟩) (.atom ⟨1, rfl⟩))))))))))))

private def eager :=
  Spelled.chain (L := exits) (.ask Op.pick (.atom later)
    (.split (stack := []) (Δ := older) (holds := .nil) [(), ()] [()] [] eagerFirst (.bind [()] eagerSecond)))

private theorem eager_normal : (eager.normal (.id older)).1 = normalWith 0 0 1 4 5 := by decide +kernel

/-- The native equation between the eager spelling and its normal form. -/
private theorem eager_native : Equiv false Γ₀ older
    (.let₁ (.op Op.pick (.bv 0))
      (.case (.bv 0)
        (.let₁ (.op Op.test (.bv 3))
          (.case (.bv 0)
            (.let₁ (.op Op.echo (.bv 0))
              (.let₁ (.op Op.mark (.bv 0)) (.let₂ (.bv 4) (.inl (.pair (.bv 1) (.bv 2))))))
            (.let₂ (.bv 0)
              (.let₁ (.op Op.mark (.bv 0)) (.let₂ (.bv 5) (.inl (.pair (.bv 1) (.bv 2))))))))
        (.let₁ (.op Op.test (.bv 3))
          (.case (.bv 0)
            (.let₁ (.op Op.echo (.bv 0)) (.let₁ (.op Op.mark (.bv 0)) (.inl (.pair (.bv 4) (.bv 1)))))
            (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 0)) (.inl (.pair (.bv 5) (.bv 1)))))))) : Term 2)
    (normalWith 0 0 1 4 5) (packedExitType exits) :=
  eager_normal ▸ spelled_equiv_normal eager

/-- The joined original and the eager spelling are natively equal. -/
example : Equiv false Γ₀ older
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.test (.bv 2))
        (.let₁ (.case (.bv 0) (.let₁ (.op Op.echo (.bv 0)) (.bv 0)) (.let₂ (.bv 0) (.bv 0)))
          (.let₁ (.op Op.mark (.bv 0))
            (.case (.bv 3)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2))))))) : Term 2)
    (.let₁ (.op Op.pick (.bv 0))
      (.case (.bv 0)
        (.let₁ (.op Op.test (.bv 3))
          (.case (.bv 0)
            (.let₁ (.op Op.echo (.bv 0))
              (.let₁ (.op Op.mark (.bv 0)) (.let₂ (.bv 4) (.inl (.pair (.bv 1) (.bv 2))))))
            (.let₂ (.bv 0)
              (.let₁ (.op Op.mark (.bv 0)) (.let₂ (.bv 5) (.inl (.pair (.bv 1) (.bv 2))))))))
        (.let₁ (.op Op.test (.bv 3))
          (.case (.bv 0)
            (.let₁ (.op Op.echo (.bv 0)) (.let₁ (.op Op.mark (.bv 0)) (.inl (.pair (.bv 4) (.bv 1)))))
            (.let₂ (.bv 0) (.let₁ (.op Op.mark (.bv 0)) (.inl (.pair (.bv 5) (.bv 1)))))))) : Term 2) (packedExitType exits) :=
  joined_normal_native.trans eager_native.symm

/-! ## Ranked validity and ordered-exit arrows

The graph is read back from the joined term itself, at the original exits.
It is not the graph of a tree of the grammar. Its validity with a tree is
decided on the expansion. -/

/-- The graph read back from the joined original. -/
private abbrev joinedGraph {t : Term 4}
    (j : SpelledJoinTags (Φ := Op) [(), ()] [()] [] [[()], [(), ()]] underS .nil 0 exits t) :
    CheckedTable Op older exits :=
  CheckedTable.ofLetCase (expanded j).exits_ne_nil (joinedTyping j)

/-- The joined original and the eager spelling are one sentence. -/
example : RankedValid false (sentenceOf (entryOf (joinedGraph (join ⟨0, rfl⟩))) (entryOf eager.graph)) :=
  (rankedValid_expanded_iff separable (joinedTyping (join ⟨0, rfl⟩)) (expanded (join ⟨0, rfl⟩))
    (joined_native (join ⟨0, rfl⟩)) eager).mpr (expanded_normal.trans eager_normal.symm)

/-- The joined original and its expansion are one sentence. -/
example : RankedValid false (sentenceOf (entryOf (joinedGraph (join ⟨0, rfl⟩)))
    (entryOf (expanded (join ⟨0, rfl⟩)).graph)) :=
  (rankedValid_expanded_iff separable (joinedTyping (join ⟨0, rfl⟩)) (expanded (join ⟨0, rfl⟩))
    (joined_native (join ⟨0, rfl⟩)) (expanded (join ⟨0, rfl⟩))).mpr rfl

/-- They have the same ordered-exit arrow at the ordered trace model with
atoms, at the original exits. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op)
      (entryOf (joinedGraph (join ⟨0, rfl⟩))) =
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf eager.graph) :=
  (denoteRanked_expanded_iff separable (joinedTyping (join ⟨0, rfl⟩)) (expanded (join ⟨0, rfl⟩))
    (joined_native (join ⟨0, rfl⟩)) eager).mpr (expanded_normal.trans eager_normal.symm)

/-! ## Variants -/

/-- The first arm supplies its payload instead of the reply of `echo`.
`mark` then takes the payload, and the second tag of `s` returns it. -/
private theorem payload_normal :
    ((expanded joinPayload).normal (.id older)).1 = normalWith 1 1 2 4 5 := by decide +kernel

/-- The second tag of `s` returns the reply of `mark` in place of its
payload. -/
private theorem arm_normal :
    ((expanded (join ⟨1, rfl⟩)).normal (.id older)).1 = normalWith 0 0 1 0 0 := by decide +kernel

/-- A changed supplied join value is observed: the joined term with the
payload supplied and the eager spelling are not one sentence. -/
private theorem supplied_apart :
    ¬ RankedValid false (sentenceOf (entryOf (joinedGraph joinPayload)) (entryOf eager.graph)) :=
  fun valid => by
    have same : normalWith 1 1 2 4 5 = normalWith 0 0 1 4 5 :=
      (payload_normal.symm.trans ((rankedValid_expanded_iff separable (joinedTyping joinPayload)
        (expanded joinPayload) (joined_native joinPayload) eager).mp valid)).trans eager_normal
    simp at same

/-- The two joined terms, which differ only in the supplied slot, are told
apart: the joined term with the payload supplied is not one sentence with
the expansion of the original. -/
example : ¬ RankedValid false (sentenceOf (entryOf (joinedGraph joinPayload))
    (entryOf (expanded (join ⟨0, rfl⟩)).graph)) :=
  fun valid => by
    have same : normalWith 1 1 2 4 5 = normalWith 0 0 1 4 5 :=
      (payload_normal.symm.trans ((rankedValid_expanded_iff separable (joinedTyping joinPayload)
        (expanded joinPayload) (joined_native joinPayload) (expanded (join ⟨0, rfl⟩))).mp valid)).trans
        expanded_normal
    simp at same

/-- A changed arm of the stored reply in the continuation is observed. -/
private theorem arm_apart :
    ¬ RankedValid false (sentenceOf (entryOf (joinedGraph (join ⟨1, rfl⟩))) (entryOf eager.graph)) :=
  fun valid => by
    have same : normalWith 0 0 1 0 0 = normalWith 0 0 1 4 5 :=
      (arm_normal.symm.trans ((rankedValid_expanded_iff separable (joinedTyping (join ⟨1, rfl⟩))
        (expanded (join ⟨1, rfl⟩)) (joined_native (join ⟨1, rfl⟩)) eager).mp valid)).trans eager_normal
    simp at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms
when the supplied join value changes. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op)
      (entryOf (joinedGraph joinPayload)) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf eager.graph) :=
  fun same => by
    have terms : normalWith 1 1 2 4 5 = normalWith 0 0 1 4 5 :=
      (payload_normal.symm.trans ((denoteRanked_expanded_iff separable (joinedTyping joinPayload)
        (expanded joinPayload) (joined_native joinPayload) eager).mp same)).trans eager_normal
    simp at terms

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
