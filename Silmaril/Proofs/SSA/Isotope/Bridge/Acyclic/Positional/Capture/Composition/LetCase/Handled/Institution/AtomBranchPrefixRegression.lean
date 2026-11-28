module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Branch.Thms

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

/-! ## A stored reply inspected after a prefix with one binary branch

There is one atom. `pick` takes one atom and replies with one of two tags:
the first carries a pair of atoms and the second one atom. `test` takes
one atom and replies with one of two tags: the first carries one atom and
the second a pair of atoms. `echo` takes one atom and replies with one
atom. Two older atoms are captured. The exits are a pair of atoms and one
atom. -/

private inductive Op | pick | test | echo
  deriving DecidableEq

local instance : TaggedSignature Unit Op where
  argument
    | .pick => .atom ()
    | .test => .atom ()
    | .echo => .atom ()
  first
    | .pick => [(), ()]
    | .test => [()]
    | .echo => [()]
  others
    | .pick => [[()]]
    | .test => [[(), ()]]
    | .echo => []

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

/-! ## The original tree

Ask `pick` on the later capture and bind its reply `s`, a slot of sum
type. While `s` is one slot, ask `test` on the earlier capture and case on
its reply at once. The two arms continue on their own.

Under the first tag of `test`, with payload `a`: ask `echo` on a chosen
atom, `a` by default, with reply `e`; then case on `s`. Under the first
tag of `s`, with payload a pair, destructure it into `x₁` and `x₂` and
return a chosen component with `e`. Under the second tag of `s`, with
payload `q`, return `q` with `a`.

Under the second tag of `test`, with payload a pair, destructure it into
`b₁` and `b₂`: ask `echo` on the later capture, with reply `f`; then case
on `s`. Under the first tag of `s` return `x₂` with `b₁`. Under the second
tag of `s` return a chosen atom, `f` by default, with `q`.

So each branch has its own request and its own two arms, and the stored
reply is inspected once on each path, after the requests of that path. -/

/-- Under the stored reply: the reply and the two captures. -/
private abbrev underS : BoundCtx (Ty Unit) 3 := older.snoc sumTy

/-- Under the first tag of `test`: `a`, the reply of `test`, `s` and the
captures; and after `echo`. -/
private abbrev armA : BoundCtx (Ty Unit) 5 := (underS.snoc testTy).snoc tok
private abbrev endA : BoundCtx (Ty Unit) 6 := armA.snoc tok
private abbrev leafAL : BoundCtx (Ty Unit) 9 := ((endA.snoc pairTy).snoc tok).snoc tok
private abbrev leafAR : BoundCtx (Ty Unit) 7 := endA.snoc tok

/-- Under the second tag of `test` after its payload is destructured:
`b₂`, `b₁`, the payload, the reply of `test`, `s` and the captures; and
after `echo`. -/
private abbrev armB : BoundCtx (Ty Unit) 7 := (((underS.snoc testTy).snoc pairTy).snoc tok).snoc tok
private abbrev endB : BoundCtx (Ty Unit) 8 := armB.snoc tok
private abbrev leafBL : BoundCtx (Ty Unit) 11 := ((endB.snoc pairTy).snoc tok).snoc tok
private abbrev leafBR : BoundCtx (Ty Unit) 9 := endB.snoc tok

/-- The arms of `s` under the first tag of `test`. -/
private def firstA (component : Slot leafAL tok) : SpelledStack (Φ := Op) [[(), ()]] (endA.snoc pairTy)
    (.cons ⟨0, rfl⟩ .nil) exits (.let₂ (.bv 0) (.inl (.pair (.bv component.1) (.bv 3))) : Term 7) :=
  .step (.atom (.done (.ret pairExit (.pair (.atom (β := leafAL) component) (.atom ⟨3, rfl⟩)))))

private def secondA : SpelledStack (Φ := Op) [[()]] leafAR (.cons ⟨0, rfl⟩ .nil) exits
    (.inl (.pair (.bv 0) (.bv 2)) : Term 7) :=
  .atom (.done (.ret pairExit (.pair (.atom (β := leafAR) ⟨0, rfl⟩) (.atom ⟨2, rfl⟩))))

/-- The arms of `s` under the second tag of `test`. -/
private def firstB : SpelledStack (Φ := Op) [[(), ()]] (endB.snoc pairTy) (.cons ⟨0, rfl⟩ .nil) exits
    (.let₂ (.bv 0) (.inl (.pair (.bv 0) (.bv 5))) : Term 9) :=
  .step (.atom (.done (.ret pairExit (.pair (.atom (β := leafBL) ⟨0, rfl⟩) (.atom ⟨5, rfl⟩)))))

private def secondB (component : Slot leafBR tok) : SpelledStack (Φ := Op) [[()]] leafBR
    (.cons ⟨0, rfl⟩ .nil) exits (.inl (.pair (.bv component.1) (.bv 0)) : Term 9) :=
  .atom (.done (.ret pairExit (.pair (.atom (β := leafBR) component) (.atom ⟨0, rfl⟩))))

/-- The tree under the stored reply: the branch on the reply of `test`,
with its two tails and their inspections of `s`. -/
private def tree (echoA : Slot armA tok) (one : Slot leafAL tok) (four : Slot leafBR tok) :
    SpelledDelay (Φ := Op) [(), ()] [()] [] underS .nil 0 exits
      (.let₁ (.op Op.test (.bv 2))
        (.case (.bv 0)
          (.let₁ (.op Op.echo (.bv echoA.1))
            (.case (.bv 3)
              (.let₂ (.bv 0) (.inl (.pair (.bv one.1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2)))))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.echo (.bv 5))
              (.case (.bv 5)
                (.let₂ (.bv 0) (.inl (.pair (.bv 0) (.bv 5))))
                (.inl (.pair (.bv four.1) (.bv 0))))))) : Term 3) :=
  .ask Op.test (.atom (β := underS) ⟨2, rfl⟩)
    (.split [()] [(), ()] []
      (.atom
        (.ask Op.echo (.atom (β := armA) echoA)
          (.bind [()] (.atom (.inspect (Δ := endA) ⟨3, rfl⟩ (firstA one) secondA)))))
      (.bind [(), ()]
        (.step
          (.atom
            (.ask Op.echo (.atom (β := armB) ⟨5, rfl⟩)
              (.bind [()] (.atom (.inspect (Δ := endB) ⟨5, rfl⟩ firstB (secondB four)))))))))

/-- The delayed tree from the original tree alone. Its term is the
original term: `test` is asked and cased on while `s` is one slot, and `s`
is cased on at the end of each branch. -/
private def built : Spelled older exits
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.test (.bv 2))
        (.case (.bv 0)
          (.let₁ (.op Op.echo (.bv 0))
            (.case (.bv 3)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2)))))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.echo (.bv 5))
              (.case (.bv 5)
                (.let₂ (.bv 0) (.inl (.pair (.bv 0) (.bv 5))))
                (.inl (.pair (.bv 1) (.bv 0)))))))) : Term 2) :=
  .chain (.ask Op.pick (.atom later)
    (SpelledStackTags.delayedTree (stack := []) (Δ := older) (holds := .nil) [(), ()] [()]
      (tree ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨1, rfl⟩)))

/-- The normal form with the chosen argument of `echo` under the first tag
of `test`, in both arms of `s`, and the chosen returned atoms. The case on
the reply of `pick` directly follows `pick`. In each of its arms `test` is
asked and cased on, and `echo` is asked in each arm of `test`: on every
path the requests are `pick`, `test`, `echo`, in that order. -/
private abbrev normalWith (echoL : Fin 8) (echoR : Fin 6) (one four : Fin 9) : Term 2 :=
  .let₁ (.op Op.pick (.bv 0))
    (.case (.bv 0)
      (.let₂ (.bv 0)
        (.let₁ (.op Op.test (.bv 5))
          (.case (.bv 0)
            (.let₁ (.op Op.echo (.bv echoL)) (.inl (.pair (.bv one) (.bv 0))))
            (.let₂ (.bv 0)
              (.let₁ (.op Op.echo (.bv 8)) (.inl (.pair (.bv 5) (.bv 2))))))))
      (.let₁ (.op Op.test (.bv 3))
        (.case (.bv 0)
          (.let₁ (.op Op.echo (.bv echoR)) (.inl (.pair (.bv 3) (.bv 1))))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.echo (.bv 6)) (.inl (.pair (.bv four) (.bv 5))))))))

private theorem built_normal : (built.normal (.id older)).1 = normalWith 0 0 4 0 := by decide +kernel

/-- The computed specialization to the first tag of `s`: under its payload
`test` is asked and cased on, `echo` is asked in each arm, and the payload
is destructured at the end of each arm. -/
example : (tree ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨1, rfl⟩).special true =
    (.let₁ (.op Op.test (.bv 3))
      (.case (.bv 0)
        (.let₁ (.op Op.echo (.bv 0)) (.let₂ (.bv 3) (.inl (.pair (.bv 1) (.bv 2)))))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.echo (.bv 6)) (.let₂ (.bv 5) (.inl (.pair (.bv 0) (.bv 4))))))) : Term 4) := by
  decide +kernel

/-- The computed specialization to the second tag of `s`. -/
example : (tree ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨1, rfl⟩).special false =
    (.let₁ (.op Op.test (.bv 3))
      (.case (.bv 0)
        (.let₁ (.op Op.echo (.bv 0)) (.inl (.pair (.bv 3) (.bv 1))))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.echo (.bv 6)) (.inl (.pair (.bv 0) (.bv 5)))))) : Term 4) := by
  decide +kernel

/-- The native equation between the built tree and its normal form. -/
private theorem built_native : Equiv false Γ₀ older
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.test (.bv 2))
        (.case (.bv 0)
          (.let₁ (.op Op.echo (.bv 0))
            (.case (.bv 3)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2)))))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.echo (.bv 5))
              (.case (.bv 5)
                (.let₂ (.bv 0) (.inl (.pair (.bv 0) (.bv 5))))
                (.inl (.pair (.bv 1) (.bv 0)))))))) : Term 2)
    (normalWith 0 0 4 0) (packedExitType exits) :=
  built_normal ▸ spelled_equiv_normal built

/-- The tree-shaped prefix equation at the computed shape: the branch
around the two cases on `s` is natively equal to the case on `s` around
the two computed specializations. -/
example : Equiv false Γ₀ underS
      (.let₁ (.op Op.test (.bv 2))
        (.case (.bv 0)
          (.let₁ (.op Op.echo (.bv 0))
            (.case (.bv 3)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2)))))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.echo (.bv 5))
              (.case (.bv 5)
                (.let₂ (.bv 0) (.inl (.pair (.bv 0) (.bv 5))))
                (.inl (.pair (.bv 1) (.bv 0))))))) : Term 3)
      (.case (.bv 0) ((tree ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨1, rfl⟩).special true)
        ((tree ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨1, rfl⟩).special false))
    (packedExitType exits) :=
  delayedTree_equiv (β := older) (stack := []) (holds := .nil) [(), ()] [()] (tree ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨1, rfl⟩)

/-! ## The eager spelling

The reply of `pick` is cased on at once. Each of its arms is written by
hand: `test` is asked and cased on with the payload of `s` packed, `echo`
is asked in each arm of `test`, and then the payload of `s` is opened. -/

private abbrev eagerP : BoundCtx (Ty Unit) 4 := underS.snoc pairTy
private abbrev eagerPA : BoundCtx (Ty Unit) 6 := (eagerP.snoc testTy).snoc tok
private abbrev eagerPAleaf : BoundCtx (Ty Unit) 9 := ((eagerPA.snoc tok).snoc tok).snoc tok
private abbrev eagerPB : BoundCtx (Ty Unit) 8 := (((eagerP.snoc testTy).snoc pairTy).snoc tok).snoc tok
private abbrev eagerPBleaf : BoundCtx (Ty Unit) 11 := ((eagerPB.snoc tok).snoc tok).snoc tok
private abbrev eagerQ : BoundCtx (Ty Unit) 4 := underS.snoc tok
private abbrev eagerQA : BoundCtx (Ty Unit) 6 := (eagerQ.snoc testTy).snoc tok
private abbrev eagerQAleaf : BoundCtx (Ty Unit) 7 := eagerQA.snoc tok
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
              (.step
                (.atom
                  (.done (.ret pairExit (.pair (.atom (β := eagerPAleaf) ⟨1, rfl⟩) (.atom ⟨2, rfl⟩))))))))))
      (.bind [(), ()]
        (.step
          (.atom
            (.ask Op.echo (.atom (β := eagerPB) ⟨6, rfl⟩)
              (.bind [()]
                (.atom
                  (.step
                    (.atom
                      (.done (.ret pairExit
                        (.pair (.atom (β := eagerPBleaf) ⟨0, rfl⟩) (.atom ⟨4, rfl⟩)))))))))))))

/-- The arm of the second tag of `s`. -/
private def eagerSecond :=
  SpelledStack.ask (L := exits) (stack := [[()]]) (Δ := eagerQ) (holds := .cons ⟨0, rfl⟩ .nil) Op.test
    (.atom (β := eagerQ) ⟨3, rfl⟩)
    (.split [()] [(), ()] []
      (.atom
        (.ask Op.echo (.atom (β := eagerQA) ⟨0, rfl⟩)
          (.bind [()]
            (.atom
              (.atom
                (.done (.ret pairExit (.pair (.atom (β := eagerQAleaf) ⟨3, rfl⟩) (.atom ⟨1, rfl⟩)))))))))
      (.bind [(), ()]
        (.step
          (.atom
            (.ask Op.echo (.atom (β := eagerQB) ⟨6, rfl⟩)
              (.bind [()]
                (.atom
                  (.atom
                    (.done (.ret pairExit
                      (.pair (.atom (β := eagerQBleaf) ⟨0, rfl⟩) (.atom ⟨5, rfl⟩))))))))))))

private def eager :=
  Spelled.chain (L := exits) (.ask Op.pick (.atom later)
    (.split (stack := []) (Δ := older) (holds := .nil) [(), ()] [()] [] eagerFirst (.bind [()] eagerSecond)))

private theorem eager_normal : (eager.normal (.id older)).1 = normalWith 0 0 4 0 := by decide +kernel


/-- The native equation between the eager spelling and its normal form.
The term of the eager spelling has `test` asked and cased on in each arm
of the case on the reply of `pick`. -/
private theorem eager_native : Equiv false Γ₀ older
    (.let₁ (.op Op.pick (.bv 0))
      (.case (.bv 0)
        (.let₁ (.op Op.test (.bv 3))
          (.case (.bv 0)
            (.let₁ (.op Op.echo (.bv 0)) (.let₂ (.bv 3) (.inl (.pair (.bv 1) (.bv 2)))))
            (.let₂ (.bv 0)
              (.let₁ (.op Op.echo (.bv 6)) (.let₂ (.bv 5) (.inl (.pair (.bv 0) (.bv 4))))))))
        (.let₁ (.op Op.test (.bv 3))
          (.case (.bv 0)
            (.let₁ (.op Op.echo (.bv 0)) (.inl (.pair (.bv 3) (.bv 1))))
            (.let₂ (.bv 0)
              (.let₁ (.op Op.echo (.bv 6)) (.inl (.pair (.bv 0) (.bv 5)))))))) : Term 2)
    (normalWith 0 0 4 0) (packedExitType exits) :=
  eager_normal ▸ spelled_equiv_normal eager

/-- The original term and the term of the eager spelling are natively
equal. -/
example : Equiv false Γ₀ older
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.test (.bv 2))
        (.case (.bv 0)
          (.let₁ (.op Op.echo (.bv 0))
            (.case (.bv 3)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2)))))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.echo (.bv 5))
              (.case (.bv 5)
                (.let₂ (.bv 0) (.inl (.pair (.bv 0) (.bv 5))))
                (.inl (.pair (.bv 1) (.bv 0)))))))) : Term 2)
    (.let₁ (.op Op.pick (.bv 0))
      (.case (.bv 0)
        (.let₁ (.op Op.test (.bv 3))
          (.case (.bv 0)
            (.let₁ (.op Op.echo (.bv 0)) (.let₂ (.bv 3) (.inl (.pair (.bv 1) (.bv 2)))))
            (.let₂ (.bv 0)
              (.let₁ (.op Op.echo (.bv 6)) (.let₂ (.bv 5) (.inl (.pair (.bv 0) (.bv 4))))))))
        (.let₁ (.op Op.test (.bv 3))
          (.case (.bv 0)
            (.let₁ (.op Op.echo (.bv 0)) (.inl (.pair (.bv 3) (.bv 1))))
            (.let₂ (.bv 0)
              (.let₁ (.op Op.echo (.bv 6)) (.inl (.pair (.bv 0) (.bv 5)))))))) : Term 2) (packedExitType exits) :=
  built_native.trans eager_native.symm

/-! ## Variants -/

private def variant (echoA : Slot armA tok) (one : Slot leafAL tok) (four : Slot leafBR tok) :=
  Spelled.chain (L := exits) (.ask Op.pick (.atom later)
    (SpelledStackTags.delayedTree (stack := []) (Δ := older) (holds := .nil) [(), ()] [()]
      (tree echoA one four)))

/-- Under the first tag of `test`, `echo` takes the later capture in place
of the payload of that tag: the behavior after the branching reply
changes. -/
private abbrev built₁ := variant ⟨3, rfl⟩ ⟨1, rfl⟩ ⟨1, rfl⟩

private theorem built₁_normal : (built₁.normal (.id older)).1 = normalWith 6 4 4 0 := by decide +kernel

/-- Under the first tag of `test` and the first tag of `s`, the other
component of the payload of `s` is returned: an arm of the stored tag
changes. -/
private abbrev built₂ := variant ⟨0, rfl⟩ ⟨0, rfl⟩ ⟨1, rfl⟩

private theorem built₂_normal : (built₂.normal (.id older)).1 = normalWith 0 0 3 0 := by decide +kernel

/-- Under the second tag of `test` and the second tag of `s`, a component
of the payload of `test` is returned in place of the reply of `echo`. -/
private abbrev built₃ := variant ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨2, rfl⟩

private theorem built₃_normal : (built₃.normal (.id older)).1 = normalWith 0 0 4 1 := by decide +kernel

/-! ## Ranked validity and ordered-exit arrows -/

private abbrev sentence {t u : Term 2} (p : Spelled older exits t) (q : Spelled older exits u) :
    RankedEquation (atomSig Unit Op) :=
  sentenceOf (entryOf p.graph) (entryOf q.graph)

/-- The built tree and the eager spelling are one sentence. -/
private theorem built_eager : RankedValid false (sentence built eager) :=
  (rankedValid_spelledTree_iff separable built eager).mpr (built_normal.trans eager_normal.symm)

/-- They have the same ordered-exit arrow at the ordered trace model with
atoms, at the original exits. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf built.graph) =
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf eager.graph) :=
  (denoteRanked_spelledTree_iff separable built eager).mpr (built_normal.trans eager_normal.symm)

/-- The behavior after the branching reply is observed. -/
private theorem branch_apart : ¬ RankedValid false (sentence built built₁) := fun valid => by
  have same : normalWith 0 0 4 0 = normalWith 6 4 4 0 :=
    (built_normal.symm.trans ((rankedValid_spelledTree_iff separable built built₁).mp valid)).trans
      built₁_normal
  simp at same

/-- The arm of the first stored tag under the first branch is observed. -/
private theorem first_apart : ¬ RankedValid false (sentence built built₂) := fun valid => by
  have same : normalWith 0 0 4 0 = normalWith 0 0 3 0 :=
    (built_normal.symm.trans ((rankedValid_spelledTree_iff separable built built₂).mp valid)).trans
      built₂_normal
  simp at same

/-- The arm of the second stored tag under the second branch is
observed. -/
private theorem second_apart : ¬ RankedValid false (sentence built built₃) := fun valid => by
  have same : normalWith 0 0 4 0 = normalWith 0 0 4 1 :=
    (built_normal.symm.trans ((rankedValid_spelledTree_iff separable built built₃).mp valid)).trans
      built₃_normal
  simp at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms
when the behavior after the branching reply changes, and when an arm of
the stored tag changes. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf built.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf built₁.graph) :=
  fun same => by
    have terms : normalWith 0 0 4 0 = normalWith 6 4 4 0 :=
      (built_normal.symm.trans ((denoteRanked_spelledTree_iff separable built built₁).mp same)).trans
        built₁_normal
    simp at terms

example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf built.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf built₃.graph) :=
  fun same => by
    have terms : normalWith 0 0 4 0 = normalWith 0 0 4 1 :=
      (built_normal.symm.trans ((denoteRanked_spelledTree_iff separable built built₃).mp same)).trans
        built₃_normal
    simp at terms

/-! ## The renaming action through the branching shape

The built tree is renamed into a context with one more capture. The action
renames the tree-shaped shape of the prefix, and the normal form of the
renamed tree, computed from the renamed tree, is the renamed normal
form. -/

private abbrev wider : BoundCtx (Ty Unit) 3 := older.snoc tok
private abbrev widen : BoundCtx.Renaming older wider := BoundCtx.Renaming.succ older tok

example : ((built.renamed widen).tree.normal (.id wider)).1 = (normalWith 0 0 4 0).rename Fin.succ := by
  decide +kernel

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
