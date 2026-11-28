module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer.Defs
public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Multi.Thms
import Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer.Layout

public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer

open PEG
open PEG.Simple.Revert.While
open EPEG.Saturation
open EPEG.Saturation.Extension

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params rest : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P params (result :: rest) n 1}
variable {body rows : List (Fin n)} {leaf : Fin n} {site : Use g}

theorem mem_uses :
    site ∈ uses g body leaf ↔ site.1 ∈ body ∧ ((g.node site.1).arg site.2).id = leaf :=
  Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer.mem_uses

theorem copySite_iff :
    copySite g body leaf = some site ↔ nullaryPrimitive g leaf = true ∧ (uses g body leaf)[1]? = some site := by
  cases h : nullaryPrimitive g leaf <;> simp [copySite, h]

theorem duplicateAt_spec {layout : Multi.Layout g}
    (found : duplicateAt g rows leaf site = some layout) :
    layout.size = rows.length + 1 ∧ List.ofFn layout.rep = rows ++ [leaf] ∧
      ∃ port : layout.Port, layout.vary = [port] ∧ layout.rep port.1 = site.1 ∧
        port.2.val = site.2.val :=
  Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer.duplicateAt_spec found

theorem duplicateAt_exists (retained : site.1 ∈ rows) :
    ∃ layout, duplicateAt g rows leaf site = some layout :=
  Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer.duplicateAt_exists retained

theorem mem_fromSlice {layout : Multi.Layout g} :
    layout ∈ fromSlice g rows body ↔ layout = shared g rows ∨
      ∃ leaf ∈ body, ∃ site, copySite g body leaf = some site ∧ duplicateAt g rows leaf site = some layout := by
  simp only [fromSlice, List.mem_cons, List.mem_filterMap, Option.bind_eq_some_iff]

theorem update_mem_sharedRows (cert : Region.Bundle.Certificate g)
    (live : leaf ∈ scheduledRows cert.scalar.update) : leaf ∈ sharedRows cert := by
  simp [sharedRows, List.mem_eraseDups, live]

/-- Each recognized copy site in the checked update contributes a layout. -/
theorem checkedSlice_has_copy {cached : Graph P params (result :: rest) n 1}
    (cert : Region.Bundle.Certificate cached)
    (live : leaf ∈ scheduledRows cert.scalar.update)
    (found : copySite g (scheduledRows cert.scalar.update) leaf = some site) :
    ∃ layout ∈ fromSlice g (sharedRows cert) (scheduledRows cert.scalar.update),
      duplicateAt g (sharedRows cert) leaf site = some layout := by
  have retained := update_mem_sharedRows cert (mem_uses.mp (List.mem_of_getElem? (copySite_iff.mp found).2)).1
  obtain ⟨layout, copied⟩ := duplicateAt_exists (leaf := leaf) retained
  exact ⟨layout, mem_fromSlice.mpr (.inr ⟨leaf, live, site, found, copied⟩), copied⟩

variable [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]

theorem mem_layouts {layout : Multi.Layout g} :
    layout ∈ layouts g ↔ ∃ cert, Region.Bundle.extract (Reindex.Automatic.cacheRows g) = some cert ∧
      layout ∈ fromSlice g (sharedRows cert) (scheduledRows cert.scalar.update) := by
  cases h : Region.Bundle.extract (Reindex.Automatic.cacheRows g) <;> simp [layouts, h]

variable {Action : Type w} {fuel : Nat}
variable {source : Output P params (result :: rest) 1}
variable {driver : Extension.Worklist.Driver (Output P params (result :: rest) 1) Action}
variable {receipt : CheckedReplay driver fuel source}
variable {cost : Candidate receipt.endpoint.2.graph → Nat}
variable {chosen : Bundle.Accepted receipt.endpoint.2.graph receipt.endpoint.2.classes}

theorem select_admitted (found : select receipt cost = some chosen) :
    chosen.candidate ∈ Multi.pool receipt.endpoint.2.classes (layouts receipt.endpoint.2.graph) ∧
      Bundle.check receipt.endpoint.2.classes chosen.candidate = some chosen :=
  Multi.select_admitted found

theorem select_min (found : select receipt cost = some chosen)
    {layout : Multi.Layout receipt.endpoint.2.graph} (listed : layout ∈ layouts receipt.endpoint.2.graph)
    {assignment : List layout.Binding} (valid : Multi.ValidAssignment receipt.endpoint.2.classes layout assignment)
    {other : Candidate receipt.endpoint.2.graph}
    (generated : Multi.materialize receipt.endpoint.2.classes layout assignment = some other)
    (admitted : (Bundle.check receipt.endpoint.2.classes other).isSome = true) :
    cost chosen.candidate ≤ cost other :=
  Multi.select_min found listed valid generated admitted

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Worklist.Generate.Infer
