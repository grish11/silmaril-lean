module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Defs
public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Thms
import Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Binding

public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate

open PEG
open EPEG (Classes)
open EPEG.Saturation
open EPEG.Saturation.Extension

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params rest : List (Ty Data)} {result t : Ty Data} {n : Nat}
variable {g : Graph P params (result :: rest) n 1}
variable {classes : Classes n} {layout : Skeleton g}
variable [DecidableEq Data]

theorem bindAt_matches (required : Ref g.sort t) {i : Fin layout.size}
    {ref : Ref (g.sort ∘ layout.rep) t} (hit : bindAt classes layout required i = some ref) :
    ref.id = i ∧ classes (layout.rep ref.id) = classes required.id :=
  Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.bindAt_matches required hit

theorem bindAt_available (required : Ref g.sort t) (i : Fin layout.size) :
    (bindAt classes layout required i).isSome = true ↔
      g.sort (layout.rep i) = t ∧ classes (layout.rep i) = classes required.id := by
  by_cases joined : classes (layout.rep i) = classes required.id <;> simp [bindAt, joined]

theorem bindFirst_available (required : Ref g.sort t) :
    (bindFirst classes layout required).isSome = true ↔
      ∃ i : Fin layout.size, g.sort (layout.rep i) = t ∧ classes (layout.rep i) = classes required.id := by
  simp only [bindFirst, List.findSome?_isSome_iff, List.mem_finRange, true_and, bindAt_available]

theorem bindFirst_matches (required : Ref g.sort t) {ref : Ref (g.sort ∘ layout.rep) t}
    (hit : bindFirst classes layout required = some ref) :
    classes (layout.rep ref.id) = classes required.id := by
  obtain ⟨_, _, bound⟩ := List.exists_of_findSome?_eq_some hit
  exact (bindAt_matches required bound).2

theorem mem_choices_none : none ∈ choices classes layout ↔ layout.vary = none := by
  cases h : layout.vary <;> simp [choices, h]

/-- All and only sort- and class-compatible target addresses appear
among the choices for the distinguished operand. -/
theorem mem_choices_some (i : Fin layout.size) :
    some i ∈ choices classes layout ↔
      ∃ focus, layout.vary = some focus ∧
        g.sort (layout.rep i) = (g.node (layout.rep focus.1)).inputs[focus.2] ∧
        classes (layout.rep i) = classes ((g.node (layout.rep focus.1)).arg focus.2).id :=
  Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.choices_some i

/-- Every successful materialization in the finite space appears in the
pool, even before the ordered selector filters for legality. -/
theorem mem_pool_iff {layouts : List (Skeleton g)} {candidate : Candidate g} :
    candidate ∈ pool classes layouts ↔
      ∃ layout ∈ layouts, ∃ choice ∈ choices classes layout, materialize classes layout choice = some candidate := by
  simp only [pool, List.mem_flatMap, List.mem_filterMap]

variable {Action : Type w} {fuel : Nat} {source : Output P params (result :: rest) 1}
variable {driver : Extension.Worklist.Driver (Output P params (result :: rest) 1) Action}
variable [∀ ins out, DecidableEq (P ins out)]
variable {receipt : CheckedReplay driver fuel source}
variable {cost : Candidate receipt.endpoint.2.graph → Nat}
variable {layouts : List (Skeleton receipt.endpoint.2.graph)}
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
    {layout : Skeleton receipt.endpoint.2.graph} (listed : layout ∈ layouts)
    {choice : Option (Fin layout.size)} (varied : choice ∈ choices receipt.endpoint.2.classes layout)
    {other : Candidate receipt.endpoint.2.graph}
    (generated : materialize receipt.endpoint.2.classes layout choice = some other)
    (admitted : (Bundle.check receipt.endpoint.2.classes other).isSome = true) :
    cost chosen.candidate ≤ cost other :=
  receipt.select_min found (mem_pool_iff.mpr ⟨layout, listed, choice, varied, generated⟩) admitted

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate
