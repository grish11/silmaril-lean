module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Spine.Thms

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

/-! ## A reply with three tags inspected after a prefix, from the prefix and the arms

There is one atom. `pick` takes one atom and replies with one of three
tags: the first carries a pair of atoms, the second one atom and the third
nothing. `duo` takes one atom and replies with a pair of atoms. `join`
takes a pair of atoms and replies with one atom. Two older atoms are
captured. The exits are a pair of atoms and one atom. -/

private inductive Op | pick | duo | join
  deriving DecidableEq

local instance : TaggedSignature Unit Op where
  argument
    | .pick => .atom ()
    | .duo => .atom ()
    | .join => .pair (.atom ()) (.atom ())
  first
    | .pick => [(), ()]
    | .duo => [(), ()]
    | .join => [()]
  others
    | .pick => [[()], []]
    | _ => []

private abbrev tok : Ty Unit := .base ()
private abbrev pairTy : Ty Unit := .product tok tok
private abbrev restTy : Ty Unit := .coprod tok .unit
private abbrev sumTy : Ty Unit := .coprod pairTy restTy
private abbrev older : BoundCtx (Ty Unit) 2 := (BoundCtx.snoc .nil tok).snoc tok
private abbrev Term (n : Nat) := LetCase.LocallyNameless.Tm Empty Op n

private theorem separable : Separable older := separable_atoms (.snoc (.snoc .nil ()) ())

private abbrev exits : List (Ty Unit) := [pairTy, tok]
private abbrev pairExit : ExitAt exits pairTy := .here

private abbrev later : Slot older tok := ⟨0, rfl⟩

/-! ## The original input

Ask `pick` on the later capture and bind its reply `s`, a slot of sum type
with three tags. The prefix runs while `s` is one slot: ask `duo` on the
earlier capture, destructure its reply into `q₁` and `q₂`, and ask `join`
on a chosen atom and the later capture, with reply `d`. With `q₁` chosen
the second request depends on the first through the pattern let. Then case
on `s`, and under its second arm case on the slot of the remaining tags.
Under the first tag, with payload a pair, destructure it into `x₁` and
`x₂` and return a chosen component with `d`. Under the second tag, with
payload `y`, return `y` with a chosen atom. Under the third tag, with no
payload, return a chosen atom with `q₁`.

Only the prefix and the three arms at its end are given. -/

/-- Under the stored reply: the reply and the two captures. -/
private abbrev underS : BoundCtx (Ty Unit) 3 := older.snoc sumTy

/-- After `duo`, after its reply is destructured, and at the end of the
prefix: `d`, `q₂`, `q₁`, the reply of `duo`, `s` and the two captures. -/
private abbrev afterDuo : BoundCtx (Ty Unit) 4 := underS.snoc pairTy
private abbrev opened : BoundCtx (Ty Unit) 6 := (afterDuo.snoc tok).snoc tok
private abbrev atEnd : BoundCtx (Ty Unit) 7 := opened.snoc tok

/-- The arm of the first tag after its payload is destructured; the slot of
the remaining tags at the end; and the arms of the second and third
tags. -/
private abbrev armL : BoundCtx (Ty Unit) 10 := ((atEnd.snoc pairTy).snoc tok).snoc tok
private abbrev atRest : BoundCtx (Ty Unit) 8 := atEnd.snoc restTy
private abbrev armM : BoundCtx (Ty Unit) 9 := atRest.snoc tok
private abbrev armU : BoundCtx (Ty Unit) 9 := atRest.snoc .unit

/-- The prefix, with the first argument of `join` chosen. -/
private def pre (first : Slot opened tok) : SpelledPrefix (Φ := Op) [] underS .nil [] atEnd .nil :=
  .ask Op.duo (.atom (β := underS) ⟨2, rfl⟩)
    (.bind [(), ()]
      (.step
        (.atom
          (.ask Op.join (.pair (.atom (β := opened) first) (.atom ⟨4, rfl⟩))
            (.bind [()] (.atom .stop))))))

/-- The arm of the first tag at the end of the prefix. -/
private def armFirst (component : Slot armL tok) : SpelledStack (Φ := Op) [[(), ()]] (atEnd.snoc pairTy)
    (.cons ⟨0, rfl⟩ .nil) exits (.let₂ (.bv 0) (.inl (.pair (.bv component.1) (.bv 3))) : Term 8) :=
  .step (.atom (.done (.ret pairExit (.pair (.atom (β := armL) component) (.atom ⟨3, rfl⟩)))))

/-- The arm of the second tag, under the slot of the remaining tags. -/
private def armSecond (component : Slot armM tok) : SpelledStack (Φ := Op) [[()]] armM
    (.cons ⟨0, rfl⟩ .nil) exits (.inl (.pair (.bv 0) (.bv component.1)) : Term 9) :=
  .atom (.done (.ret pairExit (.pair (.atom (β := armM) ⟨0, rfl⟩) (.atom component))))

/-- The arm of the third tag, under the slot of the remaining tags. -/
private def armThird (component : Slot armU tok) : SpelledStack (Φ := Op) [[]] armU
    (.cons ⟨0, rfl⟩ .nil) exits (.inl (.pair (.bv component.1) (.bv 4)) : Term 9) :=
  .unit (.done (.ret pairExit (.pair (.atom (β := armU) component) (.atom ⟨4, rfl⟩))))

/-- The arms of the second and third tags: the case on the slot of the
remaining tags at the end of the prefix. -/
private def armsRest (second : Slot armM tok) (third : Slot armU tok) :
    SpelledArms (Φ := Op) [] [[()], []] atEnd .nil exits
      (.case (.bv 0) (.inl (.pair (.bv 0) (.bv second.1))) (.inl (.pair (.bv third.1) (.bv 4))) : Term 8) :=
  .split [()] [] [] (armSecond second) (.only [] (armThird third))

/-- The delayed tree from its prefix and its three arms. Its term is the
prefix around the case on the stored reply, with the case on the remaining
tags in its second arm. -/
private def built : Spelled older exits
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.case (.bv 0)
                (.inl (.pair (.bv 0) (.bv 3)))
                (.inl (.pair (.bv 2) (.bv 4)))))))) : Term 2) :=
  .chain (.ask Op.pick (.atom later)
    (SpelledStackTags.delayedArms (stack := []) (Δ := older) (holds := .nil) [(), ()] [()] [[]]
      (pre ⟨1, rfl⟩) (armFirst ⟨1, rfl⟩) (armsRest ⟨3, rfl⟩ ⟨2, rfl⟩)))


/-- The normal form with chosen first arguments of `join` and chosen
returned pairs, one of each per tag. The case on the reply of `pick`
directly follows `pick`, the case on the remaining tags directly follows
it, and the prefix is written once in each of the three arms. -/
private abbrev normalWith (joinL : Fin 9) (joinM joinU : Fin 8) (fl sl : Fin 10) (fm sm fu su : Fin 9) :
    Term 2 :=
  .let₁ (.op Op.pick (.bv 0))
    (.case (.bv 0)
      (.let₂ (.bv 0)
        (.let₁ (.op Op.duo (.bv 5))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.join (.pair (.bv joinL) (.bv 7))) (.inl (.pair (.bv fl) (.bv sl)))))))
      (.case (.bv 0)
        (.let₁ (.op Op.duo (.bv 4))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.join (.pair (.bv joinM) (.bv 6))) (.inl (.pair (.bv fm) (.bv sm))))))
        (.let₁ (.op Op.duo (.bv 4))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.join (.pair (.bv joinU) (.bv 6))) (.inl (.pair (.bv fu) (.bv su))))))))

private theorem built_normal : (built.normal (.id older)).1 = normalWith 1 1 1 5 0 4 1 0 2 := by
  decide +kernel

/-- The computed specialization to the remaining tags has the term of the
prefix under the slot of the remaining tags, around the case on that slot
with the two arms beneath the slots of the prefix. -/
example : (pre ⟨1, rfl⟩).special restTy
      (.case (.bv 0) (.inl (.pair (.bv 0) (.bv 3))) (.inl (.pair (.bv 2) (.bv 4))) : Term 8) =
    (.let₁ (.op Op.duo (.bv 3))
      (.let₂ (.bv 0)
        (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
          (.case (.bv 4) (.inl (.pair (.bv 0) (.bv 2))) (.inl (.pair (.bv 1) (.bv 3)))))) : Term 4) := by
  decide +kernel

/-- The prefix placed under the slot of the remaining tags has that slot
beneath its own: at its end the slot is fifth, after `d`, `q₂`, `q₁` and
the reply of `duo`. The renaming that moves the slot beneath the prefix
sends it there and keeps the order of the others. -/
example : (((pre ⟨1, rfl⟩).under restTy).tree.weaken.toFun 0 : Nat) = 4 := by decide +kernel

example : (List.finRange 8).map (fun i => (((pre ⟨1, rfl⟩).past restTy).toFun i : Nat)) =
    [4, 0, 1, 2, 3, 5, 6, 7] := by decide +kernel

/-- The native equation between the built tree and its normal form. -/
private theorem built_native : Equiv false Γ₀ older
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.case (.bv 0)
                (.inl (.pair (.bv 0) (.bv 3)))
                (.inl (.pair (.bv 2) (.bv 4)))))))) : Term 2)
    (normalWith 1 1 1 5 0 4 1 0 2) (packedExitType exits) :=
  built_normal ▸ spelled_equiv_normal built

/-- The finite-prefix equation at the computed shape: the prefix around the
case is natively equal to the case around the two computed
specializations, the second of which is again a prefix around a case. -/
example : Equiv false Γ₀ underS
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.case (.bv 0)
                (.inl (.pair (.bv 0) (.bv 3)))
                (.inl (.pair (.bv 2) (.bv 4))))))) : Term 3)
      (.case (.bv 0)
        (.let₁ (.op Op.duo (.bv 3))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
              (.let₂ (.bv 4) (.inl (.pair (.bv 1) (.bv 2)))))) : Term 4)
        (.let₁ (.op Op.duo (.bv 3))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
              (.case (.bv 4) (.inl (.pair (.bv 0) (.bv 2))) (.inl (.pair (.bv 1) (.bv 3)))))) : Term 4))
    (packedExitType exits) :=
  delayedArms_equiv (β := older) (stack := []) (holds := .nil) [(), ()] [()] [[]] (pre ⟨1, rfl⟩)
    (armFirst ⟨1, rfl⟩) (armsRest ⟨3, rfl⟩ ⟨2, rfl⟩)

/-! ## The eager spelling

The reply of `pick` is cased on at once, the slot of the remaining tags is
cased on at once, and each of the three arms is written by hand with the
prefix repeated and the payload beneath its slots. -/

/-- The contexts of the three arms: with the payload bound, after the
reply of `duo` is destructured, and at the leaf. -/
private abbrev baseL : BoundCtx (Ty Unit) 4 := underS.snoc pairTy
private abbrev openedL : BoundCtx (Ty Unit) 7 := ((baseL.snoc pairTy).snoc tok).snoc tok
private abbrev leafL : BoundCtx (Ty Unit) 10 := ((openedL.snoc tok).snoc tok).snoc tok
private abbrev underRest : BoundCtx (Ty Unit) 4 := underS.snoc restTy
private abbrev baseM : BoundCtx (Ty Unit) 5 := underRest.snoc tok
private abbrev openedM : BoundCtx (Ty Unit) 8 := ((baseM.snoc pairTy).snoc tok).snoc tok
private abbrev leafM : BoundCtx (Ty Unit) 9 := openedM.snoc tok
private abbrev baseU : BoundCtx (Ty Unit) 5 := underRest.snoc .unit
private abbrev openedU : BoundCtx (Ty Unit) 8 := ((baseU.snoc pairTy).snoc tok).snoc tok
private abbrev leafU : BoundCtx (Ty Unit) 9 := openedU.snoc tok

/-- The arm of the first tag. -/
private def eagerFirst : SpelledStack (Φ := Op) [[(), ()]] baseL (.cons ⟨0, rfl⟩ .nil) exits
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.let₂ (.bv 4) (.inl (.pair (.bv 1) (.bv 2)))))) : Term 4) :=
  .ask Op.duo (.atom (β := baseL) ⟨3, rfl⟩)
    (.bind [(), ()]
      (.step
        (.atom
          (.ask Op.join (.pair (.atom (β := openedL) ⟨1, rfl⟩) (.atom ⟨5, rfl⟩))
            (.bind [()]
              (.atom
                (.step
                  (.atom
                    (.done (.ret pairExit (.pair (.atom (β := leafL) ⟨1, rfl⟩) (.atom ⟨2, rfl⟩))))))))))))

/-- The arm of the second tag. -/
private def eagerSecond : SpelledStack (Φ := Op) [[()]] baseM (.cons ⟨0, rfl⟩ .nil) exits
      (.let₁ (.op Op.duo (.bv 4))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 6))) (.inl (.pair (.bv 4) (.bv 1))))) : Term 5) :=
  .ask Op.duo (.atom (β := baseM) ⟨4, rfl⟩)
    (.bind [(), ()]
      (.step
        (.atom
          (.ask Op.join (.pair (.atom (β := openedM) ⟨1, rfl⟩) (.atom ⟨6, rfl⟩))
            (.bind [()]
              (.atom
                (.atom
                  (.done (.ret pairExit (.pair (.atom (β := leafM) ⟨4, rfl⟩) (.atom ⟨1, rfl⟩)))))))))))

/-- The arm of the third tag. -/
private def eagerThird : SpelledStack (Φ := Op) [[]] baseU (.cons ⟨0, rfl⟩ .nil) exits
      (.let₁ (.op Op.duo (.bv 4))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 6))) (.inl (.pair (.bv 0) (.bv 2))))) : Term 5) :=
  .ask Op.duo (.atom (β := baseU) ⟨4, rfl⟩)
    (.bind [(), ()]
      (.step
        (.atom
          (.ask Op.join (.pair (.atom (β := openedU) ⟨1, rfl⟩) (.atom ⟨6, rfl⟩))
            (.bind [()]
              (.atom
                (.unit
                  (.done (.ret pairExit (.pair (.atom (β := leafU) ⟨0, rfl⟩) (.atom ⟨2, rfl⟩)))))))))))

private def eager : Spelled older exits
    (.let₁ (.op Op.pick (.bv 0))
      (.case (.bv 0)
        (.let₁ (.op Op.duo (.bv 3))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
              (.let₂ (.bv 4) (.inl (.pair (.bv 1) (.bv 2)))))))
        (.case (.bv 0)
          (.let₁ (.op Op.duo (.bv 4))
            (.let₂ (.bv 0)
              (.let₁ (.op Op.join (.pair (.bv 1) (.bv 6))) (.inl (.pair (.bv 4) (.bv 1))))))
          (.let₁ (.op Op.duo (.bv 4))
            (.let₂ (.bv 0)
              (.let₁ (.op Op.join (.pair (.bv 1) (.bv 6))) (.inl (.pair (.bv 0) (.bv 2)))))))) : Term 2) :=
  .chain (.ask Op.pick (.atom later)
    (.split (stack := []) (Δ := older) (holds := .nil) [(), ()] [()] [[]] eagerFirst
      (.split (stack := []) (Δ := underS) (holds := .nil) [()] [] [] eagerSecond (.bind [] eagerThird))))

private theorem eager_normal : (eager.normal (.id older)).1 = normalWith 1 1 1 5 0 4 1 0 2 := by
  decide +kernel

/-- The native equation between the eager spelling and its normal form. -/
private theorem eager_native : Equiv false Γ₀ older
    (.let₁ (.op Op.pick (.bv 0))
      (.case (.bv 0)
        (.let₁ (.op Op.duo (.bv 3))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
              (.let₂ (.bv 4) (.inl (.pair (.bv 1) (.bv 2)))))))
        (.case (.bv 0)
          (.let₁ (.op Op.duo (.bv 4))
            (.let₂ (.bv 0)
              (.let₁ (.op Op.join (.pair (.bv 1) (.bv 6))) (.inl (.pair (.bv 4) (.bv 1))))))
          (.let₁ (.op Op.duo (.bv 4))
            (.let₂ (.bv 0)
              (.let₁ (.op Op.join (.pair (.bv 1) (.bv 6))) (.inl (.pair (.bv 0) (.bv 2)))))))) : Term 2)
    (normalWith 1 1 1 5 0 4 1 0 2) (packedExitType exits) :=
  eager_normal ▸ spelled_equiv_normal eager

/-- The original term and the term of the eager spelling are natively
equal. -/
example : Equiv false Γ₀ older
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.case (.bv 0)
                (.inl (.pair (.bv 0) (.bv 3)))
                (.inl (.pair (.bv 2) (.bv 4)))))))) : Term 2)
    (.let₁ (.op Op.pick (.bv 0))
      (.case (.bv 0)
        (.let₁ (.op Op.duo (.bv 3))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
              (.let₂ (.bv 4) (.inl (.pair (.bv 1) (.bv 2)))))))
        (.case (.bv 0)
          (.let₁ (.op Op.duo (.bv 4))
            (.let₂ (.bv 0)
              (.let₁ (.op Op.join (.pair (.bv 1) (.bv 6))) (.inl (.pair (.bv 4) (.bv 1))))))
          (.let₁ (.op Op.duo (.bv 4))
            (.let₂ (.bv 0)
              (.let₁ (.op Op.join (.pair (.bv 1) (.bv 6))) (.inl (.pair (.bv 0) (.bv 2)))))))) : Term 2) (packedExitType exits) :=
  built_native.trans eager_native.symm

/-! ## Variants -/

private def variant (first : Slot opened tok) (one : Slot armL tok) (two : Slot armM tok)
    (three : Slot armU tok) :=
  Spelled.chain (L := exits) (.ask Op.pick (.atom later)
    (SpelledStackTags.delayedArms (stack := []) (Δ := older) (holds := .nil) [(), ()] [()] [[]]
      (pre first) (armFirst one) (armsRest two three)))

/-- `join` takes the earlier capture in place of the reply of `duo`. -/
private abbrev built₁ := variant ⟨5, rfl⟩ ⟨1, rfl⟩ ⟨3, rfl⟩ ⟨2, rfl⟩

private theorem built₁_normal : (built₁.normal (.id older)).1 = normalWith 8 7 7 5 0 4 1 0 2 := by
  decide +kernel

/-- Under the first tag the other component of the payload is returned. -/
private abbrev built₂ := variant ⟨1, rfl⟩ ⟨0, rfl⟩ ⟨3, rfl⟩ ⟨2, rfl⟩

private theorem built₂_normal : (built₂.normal (.id older)).1 = normalWith 1 1 1 4 0 4 1 0 2 := by
  decide +kernel

/-- Under the second tag the other component of the reply of `duo` is
returned. -/
private abbrev built₃ := variant ⟨1, rfl⟩ ⟨1, rfl⟩ ⟨4, rfl⟩ ⟨2, rfl⟩

private theorem built₃_normal : (built₃.normal (.id older)).1 = normalWith 1 1 1 5 0 4 2 0 2 := by
  decide +kernel

/-- Under the third tag the other component of the reply of `duo` is
returned in place of `d`. -/
private abbrev built₄ := variant ⟨1, rfl⟩ ⟨1, rfl⟩ ⟨3, rfl⟩ ⟨3, rfl⟩

private theorem built₄_normal : (built₄.normal (.id older)).1 = normalWith 1 1 1 5 0 4 1 1 2 := by
  decide +kernel

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

/-- The dependency of the second request of the prefix on the first is
observed. -/
private theorem dependency_apart : ¬ RankedValid false (sentence built built₁) := fun valid => by
  have same : normalWith 1 1 1 5 0 4 1 0 2 = normalWith 8 7 7 5 0 4 1 0 2 :=
    (built_normal.symm.trans ((rankedValid_spelledTree_iff separable built built₁).mp valid)).trans
      built₁_normal
  simp at same

/-- The arm of the first tag is observed. -/
private theorem first_apart : ¬ RankedValid false (sentence built built₂) := fun valid => by
  have same : normalWith 1 1 1 5 0 4 1 0 2 = normalWith 1 1 1 4 0 4 1 0 2 :=
    (built_normal.symm.trans ((rankedValid_spelledTree_iff separable built built₂).mp valid)).trans
      built₂_normal
  simp at same

/-- The arm of the second tag is observed. -/
private theorem second_apart : ¬ RankedValid false (sentence built built₃) := fun valid => by
  have same : normalWith 1 1 1 5 0 4 1 0 2 = normalWith 1 1 1 5 0 4 2 0 2 :=
    (built_normal.symm.trans ((rankedValid_spelledTree_iff separable built built₃).mp valid)).trans
      built₃_normal
  simp at same

/-- The arm of the third tag is observed. -/
private theorem third_apart : ¬ RankedValid false (sentence built built₄) := fun valid => by
  have same : normalWith 1 1 1 5 0 4 1 0 2 = normalWith 1 1 1 5 0 4 1 1 2 :=
    (built_normal.symm.trans ((rankedValid_spelledTree_iff separable built built₄).mp valid)).trans
      built₄_normal
  simp at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms
when the arm of the third tag changes. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf built.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf built₄.graph) :=
  fun same => by
    have terms : normalWith 1 1 1 5 0 4 1 0 2 = normalWith 1 1 1 5 0 4 1 1 2 :=
      (built_normal.symm.trans ((denoteRanked_spelledTree_iff separable built built₄).mp same)).trans
        built₄_normal
    simp at terms

/-! ## The renaming action through the nested delayed cases

The built tree is renamed into a context with one more capture. The action
goes through both delayed cases, and the normal form of the renamed tree,
computed from the renamed tree, is the renamed normal form. -/

private abbrev wider : BoundCtx (Ty Unit) 3 := older.snoc tok
private abbrev widen : BoundCtx.Renaming older wider := BoundCtx.Renaming.succ older tok

example : ((built.renamed widen).tree.normal (.id wider)).1 =
    (normalWith 1 1 1 5 0 4 1 0 2).rename Fin.succ := by decide +kernel

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
