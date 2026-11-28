module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Defs

public section

namespace Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG (Classes)
open Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params rest : List (Ty Data)} {result t : Ty Data} {n : Nat}
variable {g : Graph P params (result :: rest) n 1}
variable {classes : Classes n} {layout : Skeleton g} [DecidableEq Data]

theorem bindAt_matches (required : Ref g.sort t) {i : Fin layout.size}
    {ref : Ref (g.sort ∘ layout.rep) t} (hit : bindAt classes layout required i = some ref) :
    ref.id = i ∧ classes (layout.rep ref.id) = classes required.id := by
  unfold bindAt at hit
  split at hit
  · rename_i same
    split at hit
    · cases hit
      exact ⟨rfl, same⟩
    · cases hit
  · cases hit

theorem choices_some (i : Fin layout.size) :
    some i ∈ choices classes layout ↔
      ∃ focus, layout.vary = some focus ∧
        g.sort (layout.rep i) = (g.node (layout.rep focus.1)).inputs[focus.2] ∧
        classes (layout.rep i) = classes ((g.node (layout.rep focus.1)).arg focus.2).id := by
  cases h : layout.vary with
  | none => simp [choices, h]
  | some focus =>
    simp [choices, h, bindAt]
    by_cases eq : classes (layout.rep i) = classes ((g.node (layout.rep focus.1)).arg focus.2).id
    · simp [eq]
    · simp [eq]

end Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate
