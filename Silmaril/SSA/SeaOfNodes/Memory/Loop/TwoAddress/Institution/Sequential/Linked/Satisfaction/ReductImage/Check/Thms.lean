module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Lift
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Coverage
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Composition
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.CompositeCoverage
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Diagnostic
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Thms

/-! Exact executable coverage and lifts for canonical typed valuations. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage

open CategoryTheory
open RVSDG (Port Tuple)
open CarriedAddress.Institution.RuntimeEntry (Entry)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature

variable {P Q R : EntrySignature} {cells : Nat}

theorem admitsInput_iff (cells : Nat) (args : List ValueSort) :
    admitsInput cells args = true ↔ Nonempty (Tuple (Val cells) args) :=
  Proofs.admitsInput_iff cells args

theorem admitsInput_zero_iff (args : List ValueSort) :
    admitsInput 0 args = true ↔ ValueSort.address ∉ args :=
  Proofs.admitsInput_zero_iff args

theorem checkNoIdentification_iff (h : P ⟶ Q) (sort : ValueSort) :
    checkNoIdentification h sort = true ↔ Function.Injective (fun port : Port P.args sort => h.port port) :=
  Proofs.checkNoIdentification_iff h sort

theorem checkFibres_iff (h : P ⟶ Q) (input : Tuple (Val cells) P.args) :
    checkFibres h input = true ↔ FibreConsistent h input :=
  Proofs.checkFibres_iff h input

/-- A lift exists exactly when the target tuple is inhabited and every
pair of source ports with the same image agrees on its value. -/
theorem inReductImage_iff (h : P ⟶ Q) (input : Tuple (Val cells) P.args) :
    InReductImage h input ↔ Nonempty (Tuple (Val cells) Q.args) ∧ FibreConsistent h input :=
  Proofs.inReductImage_iff h input

theorem liftInput?_sound (h : P ⟶ Q) {input : Tuple (Val cells) P.args} {target : Tuple (Val cells) Q.args}
    (lifted : liftInput? h input = some target) : reduct h ⟨cells, target⟩ = ⟨cells, input⟩ :=
  Proofs.liftInput?_sound h lifted

theorem liftInput?_isSome_iff (h : P ⟶ Q) (input : Tuple (Val cells) P.args) :
    (liftInput? h input).isSome = true ↔ InReductImage h input :=
  Proofs.liftInput?_isSome_iff h input

/-- Composite image membership requires some compatible intermediate
valuation, which the second checked lift accepts. -/
theorem inReductImage_comp_iff_lift (h : P ⟶ Q) (k : Q ⟶ R) (input : Tuple (Val cells) P.args) :
    InReductImage (h ≫ k) input ↔
      ∃ between : Tuple (Val cells) Q.args, (liftInput? k between).isSome = true ∧
        reduct h ⟨cells, between⟩ = ⟨cells, input⟩ :=
  (in_image_comp h k input).trans
    (exists_congr fun between => and_congr_left' (liftInput?_isSome_iff k between).symm)

theorem liftThrough?_isSome_iff (h : P ⟶ Q) (k : Q ⟶ R) (entry : Entry P.args cells) :
    (liftThrough? h k entry).isSome = true ↔ InReductImage (h ≫ k) entry.input := by
  simpa only [liftThrough?, Option.isSome_map] using liftInput?_isSome_iff (h ≫ k) entry.input

/-- The returned entries reduce along both maps, with the original heap
included in each equality. -/
theorem liftThrough?_sound (h : P ⟶ Q) (k : Q ⟶ R) {entry : Entry P.args cells}
    {between : Entry Q.args cells} {target : Entry R.args cells}
    (lifted : liftThrough? h k entry = some (between, target)) :
    between.reduct h = entry ∧ target.reduct k = between :=
  Proofs.liftThrough?_sound h k lifted

theorem checkCoverage_iff (h : P ⟶ Q) (cells : Nat) :
    checkCoverage h cells = true ↔ ∀ input : Tuple (Val cells) P.args, InReductImage h input :=
  Proofs.checkCoverage_iff h cells

/-- At one cell only words can distinguish identified source ports. -/
theorem checkCoverage_one (h : P ⟶ Q) : checkCoverage h 1 = checkNoIdentification h .word :=
  Proofs.checkCoverage_one h

/-- With at least two cells, the reduct is surjective exactly when the
capture map is injective within each sort. -/
theorem checkCoverage_of_two_le (h : P ⟶ Q) (two : 2 ≤ cells) :
    checkCoverage h cells = (checkNoIdentification h .word && checkNoIdentification h .address) :=
  Proofs.checkCoverage_of_two_le h two

theorem checkExpansive_iff (h : P ⟶ Q) :
    checkExpansive h = true ↔ ∀ cells (input : Tuple (Val cells) P.args), InReductImage h input :=
  Proofs.checkExpansive_iff h

theorem checkInjectiveOnImage_iff (h : P ⟶ Q) (k : Q ⟶ R) (sort : ValueSort) :
    checkInjectiveOnImage h k sort = true ↔
      Set.InjOn (fun port : Port Q.args sort => k.port port) (Set.range (fun port : Port P.args sort => h.port port)) :=
  Proofs.checkInjectiveOnImage_iff h k sort

/-- The first map must distinguish source ports, and the second map
must distinguish their images. All positions have the selected sort. -/
theorem checkNoIdentification_comp (h : P ⟶ Q) (k : Q ⟶ R) (sort : ValueSort) :
    checkNoIdentification (h ≫ k) sort = (checkNoIdentification h sort && checkInjectiveOnImage h k sort) :=
  Proofs.checkNoIdentification_comp h k sort

theorem checkCompositeCoverage_eq (h : P ⟶ Q) (k : Q ⟶ R) (cells : Nat) :
    checkCompositeCoverage h k cells = checkCoverage (h ≫ k) cells := by
  simp only [checkCompositeCoverage, checkCoverage, checkNoIdentification_comp]

theorem checkCompositeCoverage_iff (h : P ⟶ Q) (k : Q ⟶ R) (cells : Nat) :
    checkCompositeCoverage h k cells = true ↔ ∀ input : Tuple (Val cells) P.args, InReductImage (h ≫ k) input := by
  rw [checkCompositeCoverage_eq, checkCoverage_iff]

/-- Every source valuation has a compatible intermediate lift at this count. -/
theorem checkCompositeCoverage_iff_lifts (h : P ⟶ Q) (k : Q ⟶ R) (cells : Nat) :
    checkCompositeCoverage h k cells = true ↔ ∀ input : Tuple (Val cells) P.args,
      ∃ between : Tuple (Val cells) Q.args, (liftInput? k between).isSome = true ∧
        reduct h ⟨cells, between⟩ = ⟨cells, input⟩ :=
  (checkCompositeCoverage_iff h k cells).trans (forall_congr' (inReductImage_comp_iff_lift h k))

theorem checkCompositeExpansive_eq (h : P ⟶ Q) (k : Q ⟶ R) :
    checkCompositeExpansive h k = checkExpansive (h ≫ k) := by
  simp only [checkCompositeExpansive, checkExpansive, checkCompositeCoverage_eq]

theorem diagnoseCoverage?_isSome_eq (h : P ⟶ Q) (cells : Nat) :
    (diagnoseCoverage? h cells).isSome = !checkCoverage h cells :=
  Proofs.diagnoseCoverage?_isSome_eq h cells

theorem diagnoseCoverage?_valid (h : P ⟶ Q) {diagnostic : CoverageDiagnostic P Q cells}
    (found : diagnoseCoverage? h cells = some diagnostic) : diagnostic.Valid h :=
  Proofs.diagnoseCoverage?_valid h found

/-- There is an executable diagnostic exactly when the composite coverage check fails. -/
theorem diagnoseCompositeCoverage?_isSome_eq (h : P ⟶ Q) (k : Q ⟶ R) (cells : Nat) :
    (diagnoseCompositeCoverage? h k cells).isSome = !checkCompositeCoverage h k cells := by
  rw [checkCompositeCoverage_eq]
  exact diagnoseCoverage?_isSome_eq (h ≫ k) cells

theorem diagnoseCompositeCoverage?_exists_iff (h : P ⟶ Q) (k : Q ⟶ R) (cells : Nat) :
    (∃ diagnostic, diagnoseCompositeCoverage? h k cells = some diagnostic) ↔
      checkCompositeCoverage h k cells = false := by
  rw [← Option.isSome_iff_exists, diagnoseCompositeCoverage?_isSome_eq]
  simp

theorem diagnoseCompositeCoverage?_valid (h : P ⟶ Q) (k : Q ⟶ R) {diagnostic : CoverageDiagnostic P R cells}
    (found : diagnoseCompositeCoverage? h k cells = some diagnostic) : diagnostic.Valid (h ≫ k) :=
  diagnoseCoverage?_valid (h ≫ k) found

theorem CoverageDiagnostic.not_in_image (h : P ⟶ Q) {diagnostic : CoverageDiagnostic P Q cells}
    (valid : diagnostic.Valid h) : ¬ InReductImage h diagnostic.input :=
  Proofs.CoverageDiagnostic_valid_not_in_image h valid

/-- The composite entry checker rejects the diagnosed valuation for every initialized heap. -/
theorem diagnoseCompositeCoverage?_rejects (h : P ⟶ Q) (k : Q ⟶ R) {diagnostic : CoverageDiagnostic P R cells}
    (found : diagnoseCompositeCoverage? h k cells = some diagnostic) (heap : Heap cells) :
    liftThrough? h k ⟨diagnostic.input, heap⟩ = none := by
  rw [← Option.isNone_iff_eq_none, ← Option.isSome_eq_false_iff, Bool.eq_false_iff]
  intro lifted
  exact CoverageDiagnostic.not_in_image (h ≫ k) (diagnoseCompositeCoverage?_valid h k found)
    ((liftThrough?_isSome_iff h k _).mp lifted)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage
