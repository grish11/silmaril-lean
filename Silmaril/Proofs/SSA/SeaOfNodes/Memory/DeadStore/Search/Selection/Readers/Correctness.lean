module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Defs
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Proofs

open RVSDG (Tuple)

variable {args : List ValueSort} {cells : Nat}
variable {graph : Graph args} {result : Selection.Result args}

theorem rewrite_checked (input : Tuple (Val cells) args)
    (success : rewrite graph input = some result) :
    result.candidate.removeVersion ∈ Selection.storeVersions graph ∧
      discover graph result.candidate.removeVersion = some result.facts ∧
      Search.discover graph result.candidate.removeVersion result.facts = some result.candidate ∧
      Memory.DeadStore.rewrite graph result.candidate result.facts input = some result.graph := by
  obtain ⟨version, present, tried⟩ := List.exists_of_findSome?_eq_some success
  obtain ⟨facts, inferred, tried⟩ := Option.bind_eq_some_iff.mp tried
  obtain ⟨candidate, found, checked⟩ := Option.bind_eq_some_iff.mp tried
  obtain ⟨rewritten, accepted, returned⟩ := Option.bind_eq_some_iff.mp checked
  cases Option.some.inj returned
  have same := (Search.discover_sound found).1
  exact ⟨same.symm ▸ present, same.symm ▸ inferred, same.symm ▸ found, accepted⟩

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Proofs
