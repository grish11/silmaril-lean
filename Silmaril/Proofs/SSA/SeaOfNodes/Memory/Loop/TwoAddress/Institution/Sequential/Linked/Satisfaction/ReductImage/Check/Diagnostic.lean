module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Lift
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Coverage
import Silmaril.SSA.SeaOfNodes.Quads.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Proofs

open CategoryTheory
open RVSDG (Port Tuple)
open Memory.Diamond.Institution renaming Signature → EntrySignature

variable {P Q : EntrySignature} {cells : Nat} {sort : ValueSort}

private theorem findCollision?_sound (h : P ⟶ Q) {left right : Port P.args sort}
    (found : findCollision? h sort = some (left, right)) :
    h.port left = h.port right ∧ left ≠ right := by
  obtain ⟨candidate, _, picked⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨port, hit, equal⟩ := Option.map_eq_some_iff.mp picked
  cases equal
  have test := List.find?_some hit
  exact ⟨slot_eq_iff.mp (of_decide_eq_true test).1,
    fun same => (of_decide_eq_true test).2 (congrArg Quads.slot same)⟩

private theorem findCollision?_eq_none (h : P ⟶ Q) (sort : ValueSort) :
    findCollision? h sort = none ↔ checkNoIdentification h sort = true := by
  rw [findCollision?, List.findSome?_eq_none_iff, checkNoIdentification_iff]
  simp only [Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq, slot_eq_iff, not_and]
  exact ⟨fun absent _ _ same => slot_eq_iff.mp
      (not_not.mp (absent _ (portsOf_complete _) _ (portsOf_complete _) same)),
    fun injective _ _ _ _ same diff => diff (congrArg Quads.slot (injective same))⟩

private theorem checkNoIdentification_eq (h : P ⟶ Q) (sort : ValueSort) :
    checkNoIdentification h sort = !(findCollision? h sort).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [← findCollision?_eq_none]
  cases findCollision? h sort <;> simp

private theorem emptyTargetAddress (missing : admitsInput cells Q.args = false) :
    cells = 0 ∧ (portsOf .address Q.args).head?.isSome = true := by
  have zero : cells = 0 := by
    by_contra nonzero
    rw [admitsInput_positive (Nat.pos_of_ne_zero nonzero)] at missing
    cases missing
  subst cells
  have member : ValueSort.address ∈ Q.args := by
    by_contra absent
    rw [(admitsInput_zero_iff Q.args).mpr absent] at missing
    cases missing
  refine ⟨rfl, ?_⟩
  generalize Q.args = args at member ⊢
  induction args with
  | nil => simp at member
  | cons sort args ih =>
    cases sort with
    | address => rfl
    | word =>
      have tail := ih (by simpa using member)
      cases available : portsOf .address args with
      | nil => simp [available] at tail
      | cons port rest => simp [portsOf, available]

private theorem write_distinct {left right : Port P.args sort} (input : Tuple (Val cells) P.args)
    (x y : Val cells sort) (ports : left ≠ right) (values : x ≠ y) :
    let sample := Quads.write right y (Quads.write left x input)
    sample.get left ≠ sample.get right := by
  dsimp only
  rw [Quads.get_write_other _ _ _ _ (fun same => ports (slot_eq_iff.mp same)),
    Quads.get_write_same, Quads.get_write_same]
  exact values

theorem diagnoseCoverage?_valid (h : P ⟶ Q) {diagnostic : CoverageDiagnostic P Q cells}
    (found : diagnoseCoverage? h cells = some diagnostic) : diagnostic.Valid h := by
  obtain ⟨input, _, found⟩ := Option.bind_eq_some_iff.mp found
  split at found
  · rename_i missing
    cases port : (portsOf .address Q.args).head? with
    | none => simp [port] at found
    | some target =>
      simp only [port, Option.map_some, Option.some.injEq] at found
      subst diagnostic
      exact (emptyTargetAddress (by simpa using missing)).1
  · split at found
    · rename_i left right hit
      simp only [Option.some.injEq] at found
      subst diagnostic
      have ⟨same, different⟩ := findCollision?_sound h hit
      exact ⟨same, write_distinct (sort := .word) input (0 : Word) (1 : Word) different
        (by decide : (0 : Word) ≠ 1)⟩
    · split at found
      · rename_i two
        cases search : findCollision? h .address with
        | none => simp [search] at found
        | some pair =>
          obtain ⟨left, right⟩ := pair
          simp only [search, Option.map_some, Option.some.injEq] at found
          subst diagnostic
          have ⟨same, different⟩ := findCollision?_sound h search
          refine ⟨same, write_distinct input _ _ different ?_⟩
          intro equal
          have impossible := congrArg (fun address : Address cells => address.val) equal
          exact (by decide : (0 : Nat) ≠ 1) impossible
      · cases found

theorem diagnoseCoverage?_isSome_eq (h : P ⟶ Q) (cells : Nat) :
    (diagnoseCoverage? h cells).isSome = !checkCoverage h cells := by
  cases source : defaultInput? cells P.args with
  | none => simp [diagnoseCoverage?, checkCoverage, admitsInput, source]
  | some input =>
    have admitted : admitsInput cells P.args = true := by simp [admitsInput, source]
    cases target : admitsInput cells Q.args with
    | false =>
      simp [diagnoseCoverage?, checkCoverage, source, admitted, target, (emptyTargetAddress target).2]
    | true =>
      cases words : findCollision? h .word with
      | some pair =>
        obtain ⟨left, right⟩ := pair
        simp [diagnoseCoverage?, checkCoverage, source, admitted, target, checkNoIdentification_eq, words]
      | none =>
        by_cases two : 1 < cells
        · have large : ¬ cells < 2 := by omega
          simp [diagnoseCoverage?, checkCoverage, source, admitted, target, checkNoIdentification_eq,
            words, two, large]
        · have small : cells < 2 := by omega
          simp [diagnoseCoverage?, checkCoverage, source, admitted, target, checkNoIdentification_eq,
            words, two, small]

theorem CoverageDiagnostic_valid_not_in_image (h : P ⟶ Q) {diagnostic : CoverageDiagnostic P Q cells}
    (valid : diagnostic.Valid h) : ¬ InReductImage h diagnostic.input := by
  intro image
  obtain ⟨target, agrees⟩ := (inReductImage_iff h diagnostic.input).mp image
  unfold CoverageDiagnostic.Valid at valid
  split at valid
  · rename_i port _
    obtain ⟨target⟩ := target
    subst cells
    exact Fin.elim0 (target.get port)
  · rename_i _ left right _
    exact valid.2 (agrees left right valid.1)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Proofs
