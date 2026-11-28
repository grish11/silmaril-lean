module

public import Silmaril.SSA.SeaOfNodes.Memory.AddressProvenance.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.AddressProvenance.Proofs

open RVSDG (Origin Port)
open Memory.DeadStore.Search.Selection.Readers.Repeat (operations)

variable {args : List ValueSort} {past : List (List ValueSort)}

private theorem no_address_output (scope : LoadScope past) (node : Fin past.length) :
    Port past[node] .address → False := by
  induction scope with
  | start => exact node.elim0
  | @load before _ ih =>
    refine Fin.cases (motive := fun i => Port ([.word] :: before)[i] .address → False) ?_ ih node
    intro port
    cases port with
    | tail impossible => cases impossible

theorem address_argument (scope : LoadScope past) (wire : Origin args past .address) :
    ∃ port, wire = .arg port := by
  cases wire with
  | arg port => exact ⟨port, rfl⟩
  | output node port => exact (no_address_output scope node port).elim

theorem operations_argument_addresses {past : List (List ValueSort)} {version : Nat}
    (body : Body args past version) (scope : LoadScope past) :
    ∀ operation ∈ operations body, ArgumentAddress operation := by
  induction body with
  | ret => simp [operations, ArgumentAddress]
  | load _ address _ ih =>
    simp only [operations, List.mem_cons]
    intro operation member
    rcases member with rfl | later
    · exact address_argument scope address
    · exact ih (.load scope) operation later
  | store _ address _ _ ih =>
    simp only [operations, List.mem_cons]
    intro operation member
    rcases member with rfl | later
    · exact address_argument scope address
    · exact ih scope operation later

end Silmaril.SSA.SeaOfNodes.Memory.AddressProvenance.Proofs
