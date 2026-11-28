module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi.Defs
public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Thms
import Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi.Enumeration

public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi

open PEG
open EPEG (Classes)
open EPEG.Saturation
open EPEG.Saturation.Extension

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params rest : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P params (result :: rest) n 1}
variable [DecidableEq Data]
variable {classes : Classes n} {layout : Layout g}

/-- The complete product contains exactly one compatible address choice
per named port, in the supplied port order. -/
theorem mem_choices (assignment : List layout.Binding) :
    assignment ∈ choices classes layout ↔ ValidAssignment classes layout assignment :=
  Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi.mem_choices assignment

theorem resolve_assigned {assignment : List layout.Binding}
    (valid : ValidAssignment classes layout assignment) {port : layout.Port}
    {addr : Fin layout.size} (listed : (port, addr) ∈ assignment) :
    ∃ ref, resolve classes layout assignment port.1 port.2.val (layout.required port) = some ref ∧
      ref.id = addr :=
  Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi.resolve_assigned valid listed

theorem mem_pool_iff {layouts : List (Layout g)} {candidate : Candidate g} :
    candidate ∈ pool classes layouts ↔
      ∃ layout ∈ layouts, ∃ assignment : List layout.Binding,
        ValidAssignment classes layout assignment ∧ materialize classes layout assignment = some candidate := by
  simp only [pool, List.mem_flatMap, List.mem_filterMap, mem_choices]

variable {Action : Type w} {fuel : Nat} {source : Output P params (result :: rest) 1}
variable {driver : Extension.Worklist.Driver (Output P params (result :: rest) 1) Action}
variable [∀ ins out, DecidableEq (P ins out)]
variable {receipt : CheckedReplay driver fuel source}
variable {cost : Candidate receipt.endpoint.2.graph → Nat}
variable {layouts : List (Layout receipt.endpoint.2.graph)}
variable {chosen : Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes}

theorem select_admitted (found : select receipt cost layouts = some chosen) :
    chosen.candidate ∈ pool receipt.endpoint.2.classes layouts ∧
      Bundle.check receipt.endpoint.2.classes chosen.candidate = some chosen :=
  receipt.select_admitted found

theorem select_none_iff :
    select receipt cost layouts = none ↔
      ∀ candidate ∈ pool receipt.endpoint.2.classes layouts,
        Bundle.check receipt.endpoint.2.classes candidate = none :=
  Bundle.select_none_iff

theorem select_min (found : select receipt cost layouts = some chosen)
    {layout : Layout receipt.endpoint.2.graph} (listed : layout ∈ layouts)
    {assignment : List layout.Binding} (valid : ValidAssignment receipt.endpoint.2.classes layout assignment)
    {other : Candidate receipt.endpoint.2.graph}
    (generated : materialize receipt.endpoint.2.classes layout assignment = some other)
    (admitted : (Bundle.check receipt.endpoint.2.classes other).isSome = true) :
    cost chosen.candidate ≤ cost other :=
  receipt.select_min found (mem_pool_iff.mpr ⟨layout, listed, assignment, valid, generated⟩) admitted

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi
