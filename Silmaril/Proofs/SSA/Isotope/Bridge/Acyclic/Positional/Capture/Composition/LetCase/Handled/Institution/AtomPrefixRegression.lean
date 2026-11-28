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

/-! ## A reply with two tags inspected after a prefix of two requests

There is one atom. `pick` takes one atom and replies with one of two tags:
the first carries a pair of atoms and the second one atom. `duo` takes one
atom and replies with a pair of atoms. `join` takes a pair of atoms and
replies with one atom. Two older atoms are captured. The exits are a pair
of atoms and one atom. -/

private inductive Op | pick | duo | join

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

/-! ## The delayed tree

Ask `pick` on the later capture and bind its reply `s`, a slot of sum type.
Then run a prefix while `s` is one slot: ask `duo` on the earlier capture,
destructure its reply into `q₁` and `q₂`, and ask `join` on `q₁` and the
later capture, with reply `d`. So the second request of the prefix depends
on the first, through a pattern let of the prefix. Only then case on `s`.
Under the first tag, with payload a pair, destructure it into `x₁` and `x₂`
and return `x₁` with `d`. Under the second tag, with payload `y`, return
`y` with `q₂`. -/

/-- Under the stored reply: the reply and the two captures. -/
private abbrev underS : BoundCtx (Ty Unit) 3 := older.snoc sumTy

/-- After `duo`, and after its reply is destructured. -/
private abbrev afterDuo : BoundCtx (Ty Unit) 4 := underS.snoc pairTy
private abbrev opened : BoundCtx (Ty Unit) 6 := (afterDuo.snoc tok).snoc tok

/-- The contexts of the two specializations: with the payload bound, and
after the reply of `duo` is destructured. -/
private abbrev baseL : BoundCtx (Ty Unit) 4 := underS.snoc pairTy
private abbrev openedL : BoundCtx (Ty Unit) 7 := ((baseL.snoc pairTy).snoc tok).snoc tok
private abbrev baseR : BoundCtx (Ty Unit) 4 := underS.snoc tok
private abbrev openedR : BoundCtx (Ty Unit) 7 := ((baseR.snoc pairTy).snoc tok).snoc tok

/-- The leaf of the specialization to the first tag: `x₂`, `x₁`, `d`, `q₂`,
`q₁`, the reply of `duo`, the payload, the stored reply and the two
captures. The payload is beneath the slots of the prefix. -/
private abbrev leafL : BoundCtx (Ty Unit) 10 :=
  ((((((underS.snoc pairTy).snoc pairTy).snoc tok).snoc tok).snoc tok).snoc tok).snoc tok

/-- The leaf of the specialization to the second tag: `d`, `q₂`, `q₁`, the
reply of `duo`, the payload `y`, the stored reply and the two captures. -/
private abbrev leafR : BoundCtx (Ty Unit) 8 := ((((underS.snoc tok).snoc pairTy).snoc tok).snoc tok).snoc tok

/-- The normal form with chosen first arguments of `join` and chosen
returned pairs. The case on the reply of `pick` directly follows `pick`,
and the prefix is written once in each arm. -/
private abbrev normalWith (joinL : Fin 9) (joinR : Fin 7) (fl sl : Fin 10) (fr sr : Fin 8) : Term 2 :=
  .let₁ (.op Op.pick (.bv 0))
    (.case (.bv 0)
      (.let₂ (.bv 0)
        (.let₁ (.op Op.duo (.bv 5))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.join (.pair (.bv joinL) (.bv 7))) (.inl (.pair (.bv fl) (.bv sl)))))))
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv joinR) (.bv 5))) (.inl (.pair (.bv fr) (.bv sr)))))))

/-- The delayed tree. The shape of its prefix. -/
private def shape : Deferred (Φ := Op) pairTy tok underS 0
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2)))))) : Term 3)
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.let₂ (.bv 4) (.inl (.pair (.bv 1) (.bv 2)))))) : Term 4)
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.inl (.pair (.bv 4) (.bv 1))))) : Term 4) :=
  .ask Op.duo (Assembly.atom (β := underS) ⟨2, rfl⟩)
    (.unpack (Γ := afterDuo) ⟨0, rfl⟩
      (.ask Op.join (Assembly.pair (Assembly.atom (β := opened) ⟨1, rfl⟩) (Assembly.atom ⟨4, rfl⟩)) (.here rfl _ _)))

/-- Its specialization to the first tag. -/
private def left : SpelledStack (Φ := Op) [[(), ()]] (underS.snoc pairTy) (.cons ⟨0, rfl⟩ .nil) exits
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

/-- Its specialization to the second tag. -/
private def right : SpelledStackTags (Φ := Op) [] [[()]] underS .nil exits
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.inl (.pair (.bv 4) (.bv 1))))) : Term 4) :=
  .bind [()]
    (.ask Op.duo (.atom (β := baseR) ⟨3, rfl⟩)
      (.bind [(), ()]
        (.step
          (.atom
            (.ask Op.join (.pair (.atom (β := openedR) ⟨1, rfl⟩) (.atom ⟨5, rfl⟩))
              (.bind [()]
                (.atom
                  (.atom
                    (.done (.ret pairExit (.pair (.atom (β := leafR) ⟨4, rfl⟩) (.atom ⟨1, rfl⟩))))))))))))

private def delayed : Spelled older exits
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2))))))) : Term 2) :=
  .chain (.ask Op.pick (.atom later)
    (.deferred (stack := []) (Δ := older) (holds := .nil) [(), ()] [()] [] shape left right rfl rfl))

private theorem delayed_normal : (delayed.normal (.id older)).1 = normalWith 1 1 5 0 4 1 := rfl

/-- The finite-prefix equation on these terms: the prefix followed by the
case is natively equal to the case followed by the two specializations. -/
example : Equiv false Γ₀ underS
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2)))))) : Term 3)
      (.case (.bv 0)
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.let₂ (.bv 4) (.inl (.pair (.bv 1) (.bv 2)))))) : Term 4)
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.inl (.pair (.bv 4) (.bv 1))))) : Term 4))
    (packedExitType exits) :=
  deferred_equiv shape left.typing.toHasType right.typing.toHasType

/-- The native equation between the delayed tree and its normal form. -/
example : Equiv false Γ₀ older
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2))))))) : Term 2)
    (normalWith 1 1 5 0 4 1) (packedExitType exits) :=
  delayed_normal ▸ spelled_equiv_normal delayed

/-- In a larger context the normal form is the renamed normal form. -/
example : (delayed.normal (BoundCtx.Renaming.succ older tok)).1 =
    ((delayed.normal (.id older)).1).rename Fin.succ :=
  spelled_normal_rename_term delayed (.id older) (BoundCtx.Renaming.succ older tok)

/-- The eager spelling: the reply of `pick` is cased on at once, and each
arm is a specialization. It has the same normal form. -/
private def eager : Spelled older exits
    (.let₁ (.op Op.pick (.bv 0))
      (.case (.bv 0)
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.let₂ (.bv 4) (.inl (.pair (.bv 1) (.bv 2)))))) : Term 4)
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.inl (.pair (.bv 4) (.bv 1))))) : Term 4)) : Term 2) :=
  .chain (.ask Op.pick (.atom later)
    (.split (stack := []) (Δ := older) (holds := .nil) [(), ()] [()] [] left right))

private theorem eager_normal : (eager.normal (.id older)).1 = normalWith 1 1 5 0 4 1 := rfl

/-! ## Variants -/

/-- `join` takes the earlier capture in place of the reply of `duo`. The shape of its prefix. -/
private def shape₁ : Deferred (Φ := Op) pairTy tok underS 0
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 5) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2)))))) : Term 3)
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 6) (.bv 5)))
            (.let₂ (.bv 4) (.inl (.pair (.bv 1) (.bv 2)))))) : Term 4)
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 6) (.bv 5)))
            (.inl (.pair (.bv 4) (.bv 1))))) : Term 4) :=
  .ask Op.duo (Assembly.atom (β := underS) ⟨2, rfl⟩)
    (.unpack (Γ := afterDuo) ⟨0, rfl⟩
      (.ask Op.join (Assembly.pair (Assembly.atom (β := opened) ⟨5, rfl⟩) (Assembly.atom ⟨4, rfl⟩)) (.here rfl _ _)))

/-- Its specialization to the first tag. -/
private def left₁ : SpelledStack (Φ := Op) [[(), ()]] (underS.snoc pairTy) (.cons ⟨0, rfl⟩ .nil) exits
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 6) (.bv 5)))
            (.let₂ (.bv 4) (.inl (.pair (.bv 1) (.bv 2)))))) : Term 4) :=
  .ask Op.duo (.atom (β := baseL) ⟨3, rfl⟩)
    (.bind [(), ()]
      (.step
        (.atom
          (.ask Op.join (.pair (.atom (β := openedL) ⟨6, rfl⟩) (.atom ⟨5, rfl⟩))
            (.bind [()]
              (.atom
                (.step
                  (.atom
                    (.done (.ret pairExit (.pair (.atom (β := leafL) ⟨1, rfl⟩) (.atom ⟨2, rfl⟩))))))))))))

/-- Its specialization to the second tag. -/
private def right₁ : SpelledStackTags (Φ := Op) [] [[()]] underS .nil exits
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 6) (.bv 5)))
            (.inl (.pair (.bv 4) (.bv 1))))) : Term 4) :=
  .bind [()]
    (.ask Op.duo (.atom (β := baseR) ⟨3, rfl⟩)
      (.bind [(), ()]
        (.step
          (.atom
            (.ask Op.join (.pair (.atom (β := openedR) ⟨6, rfl⟩) (.atom ⟨5, rfl⟩))
              (.bind [()]
                (.atom
                  (.atom
                    (.done (.ret pairExit (.pair (.atom (β := leafR) ⟨4, rfl⟩) (.atom ⟨1, rfl⟩))))))))))))

private def delayed₁ : Spelled older exits
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 5) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2))))))) : Term 2) :=
  .chain (.ask Op.pick (.atom later)
    (.deferred (stack := []) (Δ := older) (holds := .nil) [(), ()] [()] [] shape₁ left₁ right₁ rfl rfl))

private theorem delayed₁_normal : (delayed₁.normal (.id older)).1 = normalWith 8 6 5 0 4 1 := rfl

/-- Under the first tag the other component of the payload is returned. The shape of its prefix. -/
private def shape₂ : Deferred (Φ := Op) pairTy tok underS 0
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 0) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2)))))) : Term 3)
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.let₂ (.bv 4) (.inl (.pair (.bv 0) (.bv 2)))))) : Term 4)
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.inl (.pair (.bv 4) (.bv 1))))) : Term 4) :=
  .ask Op.duo (Assembly.atom (β := underS) ⟨2, rfl⟩)
    (.unpack (Γ := afterDuo) ⟨0, rfl⟩
      (.ask Op.join (Assembly.pair (Assembly.atom (β := opened) ⟨1, rfl⟩) (Assembly.atom ⟨4, rfl⟩)) (.here rfl _ _)))

/-- Its specialization to the first tag. -/
private def left₂ : SpelledStack (Φ := Op) [[(), ()]] (underS.snoc pairTy) (.cons ⟨0, rfl⟩ .nil) exits
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.let₂ (.bv 4) (.inl (.pair (.bv 0) (.bv 2)))))) : Term 4) :=
  .ask Op.duo (.atom (β := baseL) ⟨3, rfl⟩)
    (.bind [(), ()]
      (.step
        (.atom
          (.ask Op.join (.pair (.atom (β := openedL) ⟨1, rfl⟩) (.atom ⟨5, rfl⟩))
            (.bind [()]
              (.atom
                (.step
                  (.atom
                    (.done (.ret pairExit (.pair (.atom (β := leafL) ⟨0, rfl⟩) (.atom ⟨2, rfl⟩))))))))))))

/-- Its specialization to the second tag. -/
private def right₂ : SpelledStackTags (Φ := Op) [] [[()]] underS .nil exits
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.inl (.pair (.bv 4) (.bv 1))))) : Term 4) :=
  .bind [()]
    (.ask Op.duo (.atom (β := baseR) ⟨3, rfl⟩)
      (.bind [(), ()]
        (.step
          (.atom
            (.ask Op.join (.pair (.atom (β := openedR) ⟨1, rfl⟩) (.atom ⟨5, rfl⟩))
              (.bind [()]
                (.atom
                  (.atom
                    (.done (.ret pairExit (.pair (.atom (β := leafR) ⟨4, rfl⟩) (.atom ⟨1, rfl⟩))))))))))))

private def delayed₂ : Spelled older exits
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 0) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2))))))) : Term 2) :=
  .chain (.ask Op.pick (.atom later)
    (.deferred (stack := []) (Δ := older) (holds := .nil) [(), ()] [()] [] shape₂ left₂ right₂ rfl rfl))

private theorem delayed₂_normal : (delayed₂.normal (.id older)).1 = normalWith 1 1 4 0 4 1 := rfl

/-- Under the second tag the other component of the reply of `duo` is returned. The shape of its prefix. -/
private def shape₃ : Deferred (Φ := Op) pairTy tok underS 0
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 3)))))) : Term 3)
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.let₂ (.bv 4) (.inl (.pair (.bv 1) (.bv 2)))))) : Term 4)
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.inl (.pair (.bv 4) (.bv 2))))) : Term 4) :=
  .ask Op.duo (Assembly.atom (β := underS) ⟨2, rfl⟩)
    (.unpack (Γ := afterDuo) ⟨0, rfl⟩
      (.ask Op.join (Assembly.pair (Assembly.atom (β := opened) ⟨1, rfl⟩) (Assembly.atom ⟨4, rfl⟩)) (.here rfl _ _)))

/-- Its specialization to the first tag. -/
private def left₃ : SpelledStack (Φ := Op) [[(), ()]] (underS.snoc pairTy) (.cons ⟨0, rfl⟩ .nil) exits
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

/-- Its specialization to the second tag. -/
private def right₃ : SpelledStackTags (Φ := Op) [] [[()]] underS .nil exits
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.inl (.pair (.bv 4) (.bv 2))))) : Term 4) :=
  .bind [()]
    (.ask Op.duo (.atom (β := baseR) ⟨3, rfl⟩)
      (.bind [(), ()]
        (.step
          (.atom
            (.ask Op.join (.pair (.atom (β := openedR) ⟨1, rfl⟩) (.atom ⟨5, rfl⟩))
              (.bind [()]
                (.atom
                  (.atom
                    (.done (.ret pairExit (.pair (.atom (β := leafR) ⟨4, rfl⟩) (.atom ⟨2, rfl⟩))))))))))))

private def delayed₃ : Spelled older exits
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 3))))))) : Term 2) :=
  .chain (.ask Op.pick (.atom later)
    (.deferred (stack := []) (Δ := older) (holds := .nil) [(), ()] [()] [] shape₃ left₃ right₃ rfl rfl))

private theorem delayed₃_normal : (delayed₃.normal (.id older)).1 = normalWith 1 1 5 0 4 2 := rfl

/-! ## Ranked validity and ordered-exit arrows -/

private abbrev sentence {t u : Term 2} (p : Spelled older exits t) (q : Spelled older exits u) :
    RankedEquation (atomSig Unit Op) :=
  sentenceOf (entryOf p.graph) (entryOf q.graph)

/-- The delayed tree and the eager spelling are one sentence. -/
private theorem delayed_eager : RankedValid false (sentence delayed eager) :=
  (rankedValid_spelledTree_iff separable delayed eager).mpr (delayed_normal.trans eager_normal.symm)

/-- They have the same ordered-exit arrow at the ordered trace model with
atoms. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf delayed.graph) =
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf eager.graph) :=
  (denoteRanked_spelledTree_iff separable delayed eager).mpr (delayed_normal.trans eager_normal.symm)

/-- The dependency of the second request of the prefix on the first is
observed. -/
private theorem dependency_apart : ¬ RankedValid false (sentence delayed delayed₁) := fun valid => by
  have same : normalWith 1 1 5 0 4 1 = normalWith 8 6 5 0 4 1 :=
    (delayed_normal.symm.trans ((rankedValid_spelledTree_iff separable delayed delayed₁).mp valid)).trans
      delayed₁_normal
  simp at same

/-- The branch of the first tag is observed. -/
private theorem left_apart : ¬ RankedValid false (sentence delayed delayed₂) := fun valid => by
  have same : normalWith 1 1 5 0 4 1 = normalWith 1 1 4 0 4 1 :=
    (delayed_normal.symm.trans ((rankedValid_spelledTree_iff separable delayed delayed₂).mp valid)).trans
      delayed₂_normal
  simp at same

/-- The branch of the second tag is observed. -/
private theorem right_apart : ¬ RankedValid false (sentence delayed delayed₃) := fun valid => by
  have same : normalWith 1 1 5 0 4 1 = normalWith 1 1 5 0 4 2 :=
    (delayed_normal.symm.trans ((rankedValid_spelledTree_iff separable delayed delayed₃).mp valid)).trans
      delayed₃_normal
  simp at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms,
and the model rejects each sentence. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf delayed.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf delayed₂.graph) :=
  fun same => by
    have terms : normalWith 1 1 5 0 4 1 = normalWith 1 1 4 0 4 1 :=
      (delayed_normal.symm.trans ((denoteRanked_spelledTree_iff separable delayed delayed₂).mp same)).trans
        delayed₂_normal
    simp at terms

example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf delayed.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf delayed₃.graph) :=
  fun same => by
    have terms : normalWith 1 1 5 0 4 1 = normalWith 1 1 5 0 4 2 :=
      (delayed_normal.symm.trans ((denoteRanked_spelledTree_iff separable delayed delayed₃).mp same)).trans
        delayed₃_normal
    simp at terms

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence delayed delayed₁) := fun holds =>
  dependency_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf delayed.graph)
    (entryOf delayed₁.graph) (spelled_graph delayed) (spelled_graph delayed₁)).mpr holds)

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence delayed delayed₂) := fun holds =>
  left_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf delayed.graph)
    (entryOf delayed₂.graph) (spelled_graph delayed) (spelled_graph delayed₂)).mpr holds)

example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Op))
    (atomSig Unit Op)).Sat (atomTraceRanked Unit Op) (sentence delayed delayed₃) := fun holds =>
  right_apart ((rankedValid_spelled_iff_atomTrace separable (entryOf delayed.graph)
    (entryOf delayed₃.graph) (spelled_graph delayed) (spelled_graph delayed₃)).mpr holds)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
