module

public import Silmaril.Logic.Reachability.Derivation.FirstOrder.Stock.Rebinding.Defs

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation.FirstOrder
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder.Variables
variable {Sg : FOL.Signature}
namespace Embedding
variable {k : Nat} {Γ : Fin k → Sg.S}

/-- Block realization changes no coordinate outside the proved fresh-name set. -/
theorem realizeBlock_agreeOutside (e : Embedding Γ) (M : FOL.Structure Sg)
    (a : StockAssignment M) (xs : List Sg.S) (b : BlockAssignment M xs) :
    Derivation.AgreeOutside (↑(e.freshNames xs) : Set (StockName Sg))
      a (e.realizeBlock M a xs b) := by
  classical
  induction xs with
  | nil => intro j hj; rfl
  | cons s xs ih =>
    intro j hj
    have separate : j ≠ (s, (e.extendBlock xs).fresh) ∧ j ∉ e.freshNames xs := by
      simpa only [freshNames, Finset.mem_coe, Finset.mem_insert, not_or] using hj
    have old := ih b.2 j separate.2
    have updated : (e.extendBlock xs).rebind M s (e.realizeBlock M a xs b.2) b.1 j =
        e.realizeBlock M a xs b.2 j :=
      by
        change Function.update (e.realizeBlock M a xs b.2)
          (s, (e.extendBlock xs).fresh) (show M.carrier s from b.1) j = _
        exact Function.update_of_ne separate.1 (show M.carrier s from b.1)
          (e.realizeBlock M a xs b.2)
    exact old.trans updated.symm

/-- Any agreement outside fresh names preserves every original capture exactly. -/
theorem assignment_eq_of_agreeOutside (e : Embedding Γ) (M : FOL.Structure Sg)
    (xs : List Sg.S) (a b : StockAssignment M)
    (agree : Derivation.AgreeOutside (↑(e.freshNames xs) : Set (StockName Sg)) a b) :
    e.assignment M a = e.assignment M b := by
  funext i
  exact agree (e.name i) (e.freshNames_not_old xs i)

/-- Realization leaves the old captured assignment unchanged, with no
nonempty-carrier assumption. -/
theorem assignment_realizeBlock_old (e : Embedding Γ) (M : FOL.Structure Sg)
    (a : StockAssignment M) (xs : List Sg.S) (b : BlockAssignment M xs) :
    e.assignment M (e.realizeBlock M a xs b) = e.assignment M a :=
  (e.assignment_eq_of_agreeOutside M xs a _ (e.realizeBlock_agreeOutside M a xs b)).symm

/-- Every fresh captured value is realized exactly at its sorted position. -/
theorem assignment_realizeBlock (e : Embedding Γ) (M : FOL.Structure Sg)
    (a : StockAssignment M) (xs : List Sg.S) (b : BlockAssignment M xs) :
    (e.extendBlock xs).assignment M (e.realizeBlock M a xs b) =
      joinAssignment M (e.assignment M a) xs b := by
  induction xs with
  | nil => rfl
  | cons s xs ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (e.extendBlock xs).rebind_fresh M s (e.realizeBlock M a xs b.2) b.1
    · have old := congrFun
        ((e.extendBlock xs).rebind_old M s (e.realizeBlock M a xs b.2) b.1) j
      exact old.trans (congrFun (ih b.2) j)

end Embedding

/-- Old source patterns are independent of the entire new capture block. -/
theorem Pattern.independent_freshNames {cfg : Sg.S} {k : Nat} {Γ : Fin k → Sg.S}
    (p : Pattern Sg cfg Γ) (M : FOL.Structure Sg) (e : Embedding Γ) (xs : List Sg.S) :
    Derivation.Independent (↑(e.freshNames xs) : Set (StockName Sg))
      (fun a w => Pattern.holds p M e a w) := by
  intro a b agree w
  change FOL.Formula.Holds M p (consAssignment M cfg Γ w (e.assignment M a)) ↔
    FOL.Formula.Holds M p (consAssignment M cfg Γ w (e.assignment M b))
  rw [e.assignment_eq_of_agreeOutside M xs a b agree]

/-- Exact interpretation of actual finite captured-block quantification as the
existing semantic Abstract. This is proved by constructing and projecting stock
witnesses; it is not a representability hypothesis. The current cfg is unchanged. -/
theorem Pattern.existsBlock_iff_abstract {cfg : Sg.S} {k : Nat} {Γ : Fin k → Sg.S}
    (M : FOL.Structure Sg) (e : Embedding Γ) (xs : List Sg.S)
    (p : Pattern Sg cfg (blockContext Γ xs)) (a : StockAssignment M) (w : M.carrier cfg) :
    Pattern.holds (existsBlock cfg Γ xs p) M e a w ↔
      Derivation.Abstract (↑(e.freshNames xs) : Set (StockName Sg))
        (fun b v => Pattern.holds p M (e.extendBlock xs) b v) a w := by
  change FOL.Formula.Holds M (existsBlock cfg Γ xs p)
      (consAssignment M cfg Γ w (e.assignment M a)) ↔ _
  refine (existsBlock_holds M cfg Γ xs p w (e.assignment M a)).trans ?_
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨e.realizeBlock M a xs b, e.realizeBlock_agreeOutside M a xs b, ?_⟩
    change FOL.Formula.Holds M p
      (consAssignment M cfg (blockContext Γ xs) w
        ((e.extendBlock xs).assignment M (e.realizeBlock M a xs b)))
    rw [e.assignment_realizeBlock M a xs b]
    exact hb
  · rintro ⟨b, agree, hb⟩
    refine ⟨e.blockAssignment M b xs, ?_⟩
    change FOL.Formula.Holds M p
      (consAssignment M cfg (blockContext Γ xs) w ((e.extendBlock xs).assignment M b)) at hb
    rw [e.assignment_extendBlock M b xs] at hb
    rw [e.assignment_eq_of_agreeOutside M xs a b agree]
    exact hb

end Silmaril.Logic.Reachability.Derivation.FirstOrder
