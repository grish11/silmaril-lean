module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer.Defs

public section

namespace Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate
open Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params rest : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P params (result :: rest) n 1}
variable {body rows : List (Fin n)} {leaf : Fin n} {site : Use g}

theorem mem_uses :
    site ∈ uses g body leaf ↔ site.1 ∈ body ∧ ((g.node site.1).arg site.2).id = leaf := by
  simp only [uses, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨row, live, port, _, hit⟩
    split at hit
    · rename_i same
      cases hit
      exact ⟨live, same⟩
    · cases hit
  · rintro ⟨live, same⟩
    exact ⟨site.1, live, site.2, List.mem_finRange _, by simp [same]⟩

private theorem cast_slot_val {a b : Fin n} (same : a = b) (slot : Fin (g.node a).inputs.length) :
    (same ▸ slot : Fin (g.node b).inputs.length).val = slot.val := by
  cases same
  rfl

theorem duplicateAt_spec {layout : Multi.Layout g}
    (found : duplicateAt g rows leaf site = some layout) :
    layout.size = rows.length + 1 ∧ List.ofFn layout.rep = rows ++ [leaf] ∧
      ∃ port : layout.Port, layout.vary = [port] ∧ layout.rep port.1 = site.1 ∧
        port.2.val = site.2.val := by
  unfold duplicateAt at found
  obtain ⟨i, _, chosen⟩ := List.exists_of_findSome?_eq_some found
  split at chosen
  · rename_i same
    cases chosen
    refine ⟨by simp [shared], ?_, ⟨⟨i, same.symm ▸ site.2⟩, rfl, same, ?_⟩⟩
    · exact List.ofFn_getElem
    · exact cast_slot_val same.symm site.2
  · cases chosen

theorem duplicateAt_exists (retained : site.1 ∈ rows) :
    ∃ layout, duplicateAt g rows leaf site = some layout := by
  obtain ⟨i, same⟩ := List.mem_iff_get.mp (List.mem_append_left [leaf] retained)
  apply Option.isSome_iff_exists.mp
  unfold duplicateAt
  rw [List.findSome?_isSome_iff]
  change (rows ++ [leaf])[i.val] = site.1 at same
  exact ⟨i, List.mem_finRange i, by simp [shared, same]⟩

end Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer
