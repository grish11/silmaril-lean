module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Reindex.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Reindex.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Reindex

open CategoryTheory
open RVSDG (Port Tuple)
open Diamond.Institution renaming Signature → EntrySignature
open Diamond.Institution (PortMap mapBody mapGraph pullInput)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (entryTransition run)

variable {args target : List ValueSort} {cells : Nat}
variable {facts : AddressContract args} {mapped : AddressContract target}

/-- An inequality between the anchor's cell and a listed port cannot
survive identification of that port with the anchor or any of its aliases. -/
theorem transport_refuses_collapse (rename : PortMap args target) (port : Port args .address)
    (required : port ∈ facts.disjoint.writers)
    (collapsed : rename port = rename facts.disjoint.observed ∨
      ∃ other ∈ facts.aliases, rename port = rename other) :
    facts.transport rename = none :=
  Proofs.transport_refuses_collapse rename port required collapsed

theorem valid_transport (rename : PortMap args target) (accepted : facts.transport rename = some mapped)
    (input : Tuple (Val cells) target) :
    mapped.Valid input ↔ facts.Valid (pullInput rename input) :=
  Proofs.valid_transport rename accepted input

theorem check_transport (rename : PortMap args target) (accepted : facts.transport rename = some mapped)
    (input : Tuple (Val cells) target) :
    mapped.check input = true ↔ facts.check (pullInput rename input) = true := by
  rw [mapped.check_iff_valid, facts.check_iff_valid, valid_transport rename accepted]

/-- An accepted transport preserves the nominated Store, the ordered scan
up to its first certified overwrite, and the exact retained native table. -/
theorem cut_transport (rename : PortMap args target) (transported : facts.transport rename = some mapped)
    {entry retained : Memory.Graph args} {selected : PrefixStore args} {version : Nat}
    (accepted : cut facts version entry = some (selected, retained)) :
    cut mapped version (mapBody rename entry) = some (mapStore rename selected, mapBody rename retained) :=
  Proofs.cut_transport rename transported accepted

/-- Re-emitting the current entry and diamond preserves the complete
optimized CF observations at the pulled-back invocation. The entry table
is supplied after any earlier cleanup. -/
theorem lower_observations {P Q : EntrySignature} (h : P ⟶ Q) (graph : Graph P.args) (entry : Memory.Graph P.args)
    {facts : AddressContract P.args} {mapped : AddressContract Q.args} (version : Nat)
    (transported : facts.transport (EntrySignature.Hom.port h) = some mapped)
    (input : Tuple (Val cells) Q.args) (valid : mapped.Valid input)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let pulled := pullInput (EntrySignature.Hom.port h) input
    let source := lower cells graph entry version facts
    let target := lower cells (mapGraph h graph) (mapBody (EntrySignature.Hom.port h) entry) version mapped
    entryTransition target.optimized input guard initial = entryTransition source.optimized pulled guard initial ∧
      run target.optimized input guard fuel initial = run source.optimized pulled guard fuel initial :=
  Proofs.lower_observations h graph entry version transported input valid guard fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Reindex
