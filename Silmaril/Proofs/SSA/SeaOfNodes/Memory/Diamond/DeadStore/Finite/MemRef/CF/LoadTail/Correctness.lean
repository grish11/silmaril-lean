module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.LoadTail.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.Proofs

open RVSDG (Tuple)
open DeadStore.Entry.Composition.Static
open Memory.Forwarding.Disjoint (Certificate)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)

variable {args : List ValueSort} {cells : Nat}
variable {facts : Certificate args} {input : Tuple (Val cells) args}
variable {entry retained : Memory.Graph args} {store : PrefixStore args} {version : Nat}

theorem cut_checked (accepted : cut facts version entry input = some (store, retained)) :
    facts.Valid input ∧ Final.cutWith (Final.LoadTail.checkTail facts) version entry = some (store, retained) := by
  unfold cut at accepted
  split at accepted
  next checked => exact ⟨(facts.check_iff_valid input).mp checked, accepted⟩
  next => contradiction

theorem cut_preserves (accepted : cut facts version entry input = some (store, retained)) (initial : Heap cells) :
    DeletesStores 1 (operations entry) (operations retained) ∧
      entry.denote input initial =
        ((retained.denote input initial).1, (store.table.denote input (retained.denote input initial).2).2) := by
  obtain ⟨valid, checked⟩ := cut_checked accepted
  obtain ⟨order, replay⟩ := Final.cutWith_disjoint_preserves input (Final.LoadTail.checkTail facts)
    (fun tail selected safe => Final.LoadTail.checkTail_disjoint tail selected safe valid) checked
  exact ⟨order, replay PUnit.unit initial⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.Proofs
