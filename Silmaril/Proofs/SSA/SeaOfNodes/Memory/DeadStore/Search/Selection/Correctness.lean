module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Defs
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Proofs

open RVSDG (Tuple)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}
variable {graph : Graph args} {certificates : List (Certificate args)} {result : Result args}

theorem rewrite_checked (input : Tuple (Val cells) args)
    (success : rewrite graph certificates input = some result) :
    result.candidate.removeVersion ∈ storeVersions graph ∧
      result.facts ∈ certificates ∧
      Search.discover graph result.candidate.removeVersion result.facts = some result.candidate ∧
      Memory.DeadStore.rewrite graph result.candidate result.facts input = some result.graph := by
  obtain ⟨version, present, scanned⟩ := List.exists_of_findSome?_eq_some success
  obtain ⟨facts, supplied, tried⟩ := List.exists_of_findSome?_eq_some scanned
  obtain ⟨candidate, discovered, checked⟩ := Option.bind_eq_some_iff.mp tried
  obtain ⟨rewritten, accepted, returned⟩ := Option.bind_eq_some_iff.mp checked
  cases Option.some.inj returned
  have same := (Search.discover_sound discovered).1
  exact ⟨same.symm ▸ present, supplied, same.symm ▸ discovered, accepted⟩

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Proofs
