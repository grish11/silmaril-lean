module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Proofs

open RVSDG (Tuple)

variable {args : List ValueSort} {cells : Nat}
variable {source : Prefixed args} {result : Result args}

theorem rewrite_checked (input : Tuple (Val cells) args) (success : rewrite source input = some result) :
    (∀ arrival, discoverSlot source arrival = some (result.candidate arrival)) ∧
      DeadStore.rewrite source result.candidate input = some result.graph := by
  obtain ⟨candidate, found, rewritten⟩ := Option.bind_eq_some_iff.mp success
  obtain ⟨graph, checked, returned⟩ := Option.bind_eq_some_iff.mp rewritten
  cases Option.some.inj returned
  obtain ⟨first, foundFirst, next⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨second, foundSecond, matched⟩ := Option.bind_eq_some_iff.mp next
  cases Option.some.inj matched
  exact ⟨fun arrival => by cases arrival <;> assumption, checked⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Proofs
