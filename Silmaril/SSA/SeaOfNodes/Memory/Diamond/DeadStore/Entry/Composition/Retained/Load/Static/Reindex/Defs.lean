module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Defs

/-! Transport the static diamond entry contract along typed input maps. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static

open Diamond.Institution (PortMap)

variable {args target : List ValueSort}

def AddressContract.mapPorts (facts : AddressContract args) (rename : PortMap args target) :
    AddressContract target :=
  ⟨⟨rename facts.disjoint.observed, facts.disjoint.writers.map (fun p => rename p)⟩,
    facts.aliases.map (fun p => rename p)⟩

/-- Rename the anchor and both fact lists. A required disjoint port must
remain distinct from the anchor and every listed alias. Other ports may
be identified, including ports required to denote the same cell. -/
def AddressContract.transport (facts : AddressContract args) (rename : PortMap args target) :
    Option (AddressContract target) :=
  let mapped := facts.mapPorts rename
  if mapped.consistent then some mapped else none

namespace Reindex

def mapStore (rename : PortMap args target) (store : PrefixStore args) : PrefixStore target :=
  ⟨rename store.address, rename store.value⟩

end Reindex
end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static
