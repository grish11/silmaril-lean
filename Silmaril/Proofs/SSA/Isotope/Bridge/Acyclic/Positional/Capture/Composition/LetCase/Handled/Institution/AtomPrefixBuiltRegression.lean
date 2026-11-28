module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Renaming.Thms

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

/-! ## A delayed case built from its prefix and its arms

There is one atom. `pick` takes one atom and replies with one of two tags:
the first carries a pair of atoms and the second one atom. `duo` takes one
atom and replies with a pair of atoms. `join` takes a pair of atoms and
replies with one atom. Two older atoms are captured. The exits are a pair
of atoms and one atom. -/

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

/-! ## The original input

Ask `pick` on the later capture and bind its reply `s`, a slot of sum type.
The prefix runs while `s` is one slot: ask `duo` on the earlier capture,
destructure its reply into `q₁` and `q₂`, and ask `join` on a chosen atom
and the later capture, with reply `d`. With `q₁` chosen the second request
depends on the first through the pattern let. Then case on `s`. Under the
first tag, with payload a pair, destructure it into `x₁` and `x₂` and
return a chosen component with `d`. Under the second tag, with payload
`y`, return `y` with a chosen component of the reply of `duo`.

Only the prefix and the two arms at its end are given. The shape of the
prefix and the two specializations are computed. -/

/-- Under the stored reply: the reply and the two captures. -/
private abbrev underS : BoundCtx (Ty Unit) 3 := older.snoc sumTy

/-- After `duo`, after its reply is destructured, and at the end of the
prefix: `d`, `q₂`, `q₁`, the reply of `duo`, `s` and the two captures. -/
private abbrev afterDuo : BoundCtx (Ty Unit) 4 := underS.snoc pairTy
private abbrev opened : BoundCtx (Ty Unit) 6 := (afterDuo.snoc tok).snoc tok
private abbrev atEnd : BoundCtx (Ty Unit) 7 := opened.snoc tok

/-- The arm of the first tag after its payload is destructured, and the
arm of the second tag. -/
private abbrev armL : BoundCtx (Ty Unit) 10 := ((atEnd.snoc pairTy).snoc tok).snoc tok
private abbrev armR : BoundCtx (Ty Unit) 8 := atEnd.snoc tok

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

/-- The arm of the second tag at the end of the prefix. -/
private def armSecond (component : Slot armR tok) : SpelledStack (Φ := Op) [[()]] (atEnd.snoc tok)
    (.cons ⟨0, rfl⟩ .nil) exits (.inl (.pair (.bv 0) (.bv component.1)) : Term 8) :=
  .atom (.done (.ret pairExit (.pair (.atom (β := armR) ⟨0, rfl⟩) (.atom component))))

/-- The delayed tree from its prefix and its two arms. Its term is the
prefix around the case on the stored reply. -/
private def built : Spelled older exits
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2))))))) : Term 2) :=
  .chain (.ask Op.pick (.atom later)
    (SpelledStackTags.delayed (stack := []) (Δ := older) (holds := .nil) [(), ()] [()]
      (pre ⟨1, rfl⟩) (armFirst ⟨1, rfl⟩) (armSecond ⟨2, rfl⟩)))

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

/-- The computed specializations have the terms of the specializations
written by hand: the prefix under the payload of the tag, around the arm
with the payload beneath the slots of the prefix. -/
example : (pre ⟨1, rfl⟩).special pairTy (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))) : Term 8) =
    (.let₁ (.op Op.duo (.bv 3))
      (.let₂ (.bv 0)
        (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
          (.let₂ (.bv 4) (.inl (.pair (.bv 1) (.bv 2)))))) : Term 4) := rfl

example : (pre ⟨1, rfl⟩).special tok (.inl (.pair (.bv 0) (.bv 2)) : Term 8) =
    (.let₁ (.op Op.duo (.bv 3))
      (.let₂ (.bv 0)
        (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
          (.inl (.pair (.bv 4) (.bv 1))))) : Term 4) := rfl

private theorem built_normal : (built.normal (.id older)).1 = normalWith 1 1 5 0 4 1 := by decide +kernel

/-- The native equation between the built tree and its normal form. -/
example : Equiv false Γ₀ older
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2))))))) : Term 2)
    (normalWith 1 1 5 0 4 1) (packedExitType exits) :=
  built_normal ▸ spelled_equiv_normal built

/-- The finite-prefix equation at the computed shape: the prefix around the
case is natively equal to the case around the computed specializations. -/
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
  delayed_equiv (β := older) (stack := []) (holds := .nil) [(), ()] [()] (pre ⟨1, rfl⟩) (armFirst ⟨1, rfl⟩)
    (armSecond ⟨2, rfl⟩)

/-! ## The eager spelling

The reply of `pick` is cased on at once, and each arm is a specialization
written by hand, with the prefix repeated and the payload beneath its
slots. -/

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

/-- `join` takes the earlier capture in place of the reply of `duo`. -/
private def built₁ :=
  Spelled.chain (L := exits) (.ask Op.pick (.atom later)
    (SpelledStackTags.delayed (stack := []) (Δ := older) (holds := .nil) [(), ()] [()]
      (pre ⟨5, rfl⟩) (armFirst ⟨1, rfl⟩) (armSecond ⟨2, rfl⟩)))

private theorem built₁_normal : (built₁.normal (.id older)).1 = normalWith 8 6 5 0 4 1 := by decide +kernel

/-- Under the first tag the other component of the payload is returned. -/
private def built₂ :=
  Spelled.chain (L := exits) (.ask Op.pick (.atom later)
    (SpelledStackTags.delayed (stack := []) (Δ := older) (holds := .nil) [(), ()] [()]
      (pre ⟨1, rfl⟩) (armFirst ⟨0, rfl⟩) (armSecond ⟨2, rfl⟩)))

private theorem built₂_normal : (built₂.normal (.id older)).1 = normalWith 1 1 4 0 4 1 := by decide +kernel

/-- Under the second tag the other component of the reply of `duo` is
returned. -/
private def built₃ :=
  Spelled.chain (L := exits) (.ask Op.pick (.atom later)
    (SpelledStackTags.delayed (stack := []) (Δ := older) (holds := .nil) [(), ()] [()]
      (pre ⟨1, rfl⟩) (armFirst ⟨1, rfl⟩) (armSecond ⟨3, rfl⟩)))

private theorem built₃_normal : (built₃.normal (.id older)).1 = normalWith 1 1 5 0 4 2 := by decide +kernel

/-- The reply of `duo` is selected on the stack before it is destructured.
The selection does not change the term or the normal form. -/
private def preSelected : SpelledPrefix (Φ := Op) [] underS .nil [] atEnd .nil :=
  .ask Op.duo (.atom (β := underS) ⟨2, rfl⟩)
    (.bind [(), ()]
      (.pick .here
        (.step
          (.atom
            (.ask Op.join (.pair (.atom (β := opened) ⟨1, rfl⟩) (.atom ⟨4, rfl⟩))
              (.bind [()] (.atom .stop)))))))

private def built₄ : Spelled older exits
    (.let₁ (.op Op.pick (.bv 0))
      (.let₁ (.op Op.duo (.bv 2))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 4)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2))))))) : Term 2) :=
  .chain (.ask Op.pick (.atom later)
    (SpelledStackTags.delayed (stack := []) (Δ := older) (holds := .nil) [(), ()] [()]
      preSelected (armFirst ⟨1, rfl⟩) (armSecond ⟨2, rfl⟩)))

private theorem built₄_normal : (built₄.normal (.id older)).1 = normalWith 1 1 5 0 4 1 := by decide +kernel

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
  have same : normalWith 1 1 5 0 4 1 = normalWith 8 6 5 0 4 1 :=
    (built_normal.symm.trans ((rankedValid_spelledTree_iff separable built built₁).mp valid)).trans
      built₁_normal
  simp at same

/-- The arm of the first tag is observed. -/
private theorem left_apart : ¬ RankedValid false (sentence built built₂) := fun valid => by
  have same : normalWith 1 1 5 0 4 1 = normalWith 1 1 4 0 4 1 :=
    (built_normal.symm.trans ((rankedValid_spelledTree_iff separable built built₂).mp valid)).trans
      built₂_normal
  simp at same

/-- The arm of the second tag is observed. -/
private theorem right_apart : ¬ RankedValid false (sentence built built₃) := fun valid => by
  have same : normalWith 1 1 5 0 4 1 = normalWith 1 1 5 0 4 2 :=
    (built_normal.symm.trans ((rankedValid_spelledTree_iff separable built built₃).mp valid)).trans
      built₃_normal
  simp at same

/-- The ordered-exit arrows differ at the ordered trace model with atoms
when an arm changes. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf built.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Op)) (atomTraceModel Unit Op) (entryOf built₂.graph) :=
  fun same => by
    have terms : normalWith 1 1 5 0 4 1 = normalWith 1 1 4 0 4 1 :=
      (built_normal.symm.trans ((denoteRanked_spelledTree_iff separable built built₂).mp same)).trans
        built₂_normal
    simp at terms

/-! ## The renaming action

The built tree and the eager spelling are renamed into a context with one
more capture. The terms are the renamed terms, the normal forms are the
renamed normal forms, and the renamed trees are one sentence there. -/

private abbrev wider : BoundCtx (Ty Unit) 3 := older.snoc tok
private abbrev widen : BoundCtx.Renaming older wider := BoundCtx.Renaming.succ older tok

private theorem separableWider : Separable wider := separable_atoms (.snoc (.snoc (.snoc .nil ()) ()) ())

/-- The term of the renamed tree, computed: the captures are the two older
of three. -/
example : (built.renamed widen).term =
    (.let₁ (.op Op.pick (.bv 1))
      (.let₁ (.op Op.duo (.bv 3))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv 1) (.bv 5)))
            (.case (.bv 4)
              (.let₂ (.bv 0) (.inl (.pair (.bv 1) (.bv 3))))
              (.inl (.pair (.bv 0) (.bv 2))))))) : Term 3) := by decide +kernel

/-- The normal form in the wider context with chosen first arguments of
`join` and chosen returned pairs. -/
private abbrev wideWith (joinL : Fin 10) (joinR : Fin 8) (fl sl : Fin 11) (fr sr : Fin 9) : Term 3 :=
  .let₁ (.op Op.pick (.bv 1))
    (.case (.bv 0)
      (.let₂ (.bv 0)
        (.let₁ (.op Op.duo (.bv 6))
          (.let₂ (.bv 0)
            (.let₁ (.op Op.join (.pair (.bv joinL) (.bv 8))) (.inl (.pair (.bv fl) (.bv sl)))))))
      (.let₁ (.op Op.duo (.bv 4))
        (.let₂ (.bv 0)
          (.let₁ (.op Op.join (.pair (.bv joinR) (.bv 6))) (.inl (.pair (.bv fr) (.bv sr)))))))

private theorem wide_normal : (normalWith 1 1 5 0 4 1).rename Fin.succ = wideWith 1 1 5 0 4 1 := by
  decide +kernel

private theorem wide₂_normal : (normalWith 1 1 4 0 4 1).rename Fin.succ = wideWith 1 1 4 0 4 1 := by
  decide +kernel

/-- The normal form of the renamed tree, computed from the renamed tree. -/
example : ((built.renamed widen).tree.normal (.id wider)).1 = wideWith 1 1 5 0 4 1 := by decide +kernel

/-- It is the renamed normal form. -/
example : ((built.renamed widen).tree.normal (.id wider)).1 = (normalWith 1 1 5 0 4 1).rename Fin.succ :=
  (congrArg Sigma.fst (spelled_renamed_normal_id built widen)).trans
    ((spelled_normal_rename_term built (.id older) widen).trans
      (congrArg (fun x : Term 2 => x.rename Fin.succ) built_normal))

/-- The renamed trees are one sentence in the wider context. -/
example : RankedValid false
    (sentenceOf (entryOf (built.renamed widen).tree.graph) (entryOf (eager.renamed widen).tree.graph)) :=
  (rankedValid_spelled_renamed_iff separableWider built eager widen).mpr
    ((spelled_normal_rename_term built (.id older) widen).trans
      ((congrArg (fun x : Term 2 => x.rename Fin.succ) (built_normal.trans eager_normal.symm)).trans
        (spelled_normal_rename_term eager (.id older) widen).symm))

/-- A changed arm stays apart after renaming. -/
example : ¬ RankedValid false
    (sentenceOf (entryOf (built.renamed widen).tree.graph) (entryOf (built₂.renamed widen).tree.graph)) :=
  fun valid => by
    have same := (rankedValid_spelled_renamed_iff separableWider built built₂ widen).mp valid
    have terms : wideWith 1 1 5 0 4 1 = wideWith 1 1 4 0 4 1 :=
      (wide_normal.symm.trans (((congrArg (fun x : Term 2 => x.rename Fin.succ) built_normal).symm.trans
        ((spelled_normal_rename_term built (.id older) widen).symm.trans (same.trans
          (spelled_normal_rename_term built₂ (.id older) widen)))).trans
        (congrArg (fun x : Term 2 => x.rename Fin.succ) built₂_normal))).trans wide₂_normal
    simp at terms

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
