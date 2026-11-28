module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Lift
import Silmaril.SSA.SeaOfNodes.Quads.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Proofs

open CategoryTheory
open RVSDG (Port Tuple)
open Memory.Diamond.Institution renaming Signature → EntrySignature

variable {P Q : EntrySignature} {cells : Nat}

theorem admitsInput_zero_iff (args : List ValueSort) :
    admitsInput 0 args = true ↔ ValueSort.address ∉ args := by
  induction args with
  | nil => simp [admitsInput, defaultInput?]
  | cons sort args ih =>
    cases sort with
    | word => simpa [admitsInput, defaultInput?] using ih
    | address => simp [admitsInput, defaultInput?]

theorem admitsInput_positive (positive : 0 < cells) (args : List ValueSort) :
    admitsInput cells args = true := by
  induction args with
  | nil => rfl
  | cons sort args ih => cases sort <;> simpa [admitsInput, defaultInput?, positive] using ih

private theorem injective_of_coverage (h : P ⟶ Q) (sort : ValueSort) (base : Tuple (Val cells) P.args)
    (x y : Val cells sort) (distinct : x ≠ y) (covers : ∀ input : Tuple (Val cells) P.args, InReductImage h input) :
    Function.Injective (fun port : Port P.args sort => h.port port) := by
  intro left right identified
  by_contra different
  let sample := Quads.write right y (Quads.write left x base)
  have agree := (inReductImage_iff h sample).mp (covers sample) |>.2 left right identified
  change (Quads.write right y (Quads.write left x base)).get left =
    (Quads.write right y (Quads.write left x base)).get right at agree
  rw [Quads.get_write_other _ _ _ _ (fun same => different (slot_eq_iff.mp same)),
    Quads.get_write_same, Quads.get_write_same] at agree
  exact distinct agree

private theorem address_eq (small : cells < 2) (left right : Address cells) : left = right := by
  apply Fin.ext
  have leftBound := left.isLt
  have rightBound := right.isLt
  omega

theorem checkCoverage_iff (h : P ⟶ Q) (cells : Nat) :
    checkCoverage h cells = true ↔ ∀ input : Tuple (Val cells) P.args, InReductImage h input := by
  cases source : admitsInput cells P.args with
  | false =>
    simp only [checkCoverage, source, Bool.not_false, Bool.true_or, true_iff]
    intro input
    have yes := (admitsInput_iff cells P.args).mpr ⟨input⟩
    rw [source] at yes
    cases yes
  | true =>
    simp only [checkCoverage, source, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
      admitsInput_iff, checkNoIdentification_iff, decide_eq_true_eq]
    constructor
    · rintro ⟨target, words, addresses⟩ input
      refine (inReductImage_iff h input).mpr ⟨target, ?_⟩
      intro sort left right identified
      cases sort with
      | word => exact congrArg input.get (words identified)
      | address =>
        rcases addresses with small | injective
        · exact address_eq small (input.get left) (input.get right)
        · exact congrArg input.get (injective identified)
    · intro covers
      obtain ⟨base⟩ := (admitsInput_iff cells P.args).mp source
      refine ⟨((inReductImage_iff h base).mp (covers base)).1,
        injective_of_coverage h .word base (0 : Word) (1 : Word) (by decide : (0 : Word) ≠ 1) covers, ?_⟩
      by_cases small : cells < 2
      · exact Or.inl small
      · have positive : 0 < cells := by omega
        have two : 1 < cells := by omega
        refine Or.inr (injective_of_coverage h .address base ⟨0, positive⟩ ⟨1, two⟩ ?_ covers)
        intro equal
        have impossible := congrArg (fun address : Address cells => address.val) equal
        exact (by decide : (0 : Nat) ≠ 1) impossible

theorem checkCoverage_one (h : P ⟶ Q) : checkCoverage h 1 = checkNoIdentification h .word := by
  simp [checkCoverage, admitsInput_positive (cells := 1) (by decide)]

theorem checkCoverage_of_two_le (h : P ⟶ Q) (two : 2 ≤ cells) :
    checkCoverage h cells = (checkNoIdentification h .word && checkNoIdentification h .address) := by
  simp [checkCoverage, admitsInput_positive (cells := cells) (by omega), Nat.not_lt.mpr two]

theorem checkExpansive_iff (h : P ⟶ Q) :
    checkExpansive h = true ↔ ∀ cells (input : Tuple (Val cells) P.args), InReductImage h input := by
  simp only [checkExpansive, Bool.and_eq_true]
  constructor
  · rintro ⟨zero, two⟩ cells
    rw [checkCoverage_of_two_le h (by decide : 2 ≤ 2)] at two
    apply (checkCoverage_iff h cells).mp
    match cells with
    | 0 => exact zero
    | 1 => exact (checkCoverage_one h).trans (Bool.and_eq_true_iff.mp two).1
    | n + 2 => exact (checkCoverage_of_two_le h (show 2 ≤ n + 2 by omega)).trans two
  · intro all
    exact ⟨(checkCoverage_iff h 0).mpr (all 0), (checkCoverage_iff h 2).mpr (all 2)⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Proofs
