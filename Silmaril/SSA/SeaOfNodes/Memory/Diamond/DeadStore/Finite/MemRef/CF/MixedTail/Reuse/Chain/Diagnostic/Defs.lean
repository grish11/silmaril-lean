module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Defs

/-! Explain the first refusal when rechecking an admitted mixed-entry chain. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Diagnostic

open RVSDG (Port Tuple)
open Quads.CFG (Predecessors)
open Memory.Forwarding.Disjoint (cell)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}

/-- Zero-based access in the retained entry suffix, or reader before an
overwrite in a particular Region occurrence. -/
inductive Site (preds : Predecessors sites) where
  | entry (access : Nat)
  | arm (occurrence : Occurrence preds) (reader : Nat)

def Site.portAt (site : Site preds) (stage : MixedTail.Result cells args preds) :
    Option (Port args .address) :=
  match site with
  | .entry access => stage.ports[access]?
  | .arm occurrence reader => (stage.candidate occurrence).readers[reader]?

/-- Entry accesses first, then occurrences in Region order and readers in
each occurrence's recorded order. -/
def obligations (stage : MixedTail.Result cells args preds) : List (Site preds × Port args .address) :=
  (stage.ports.zipIdx.map fun (port, index) => (.entry index, port)) ++
    (List.finRange (preds.rest.length + 1)).flatMap fun occurrence =>
      (stage.candidate occurrence).readers.zipIdx.map fun (port, index) => (.arm occurrence index, port)

structure Alias (cells : Nat) (args : List ValueSort) (preds : Predecessors sites) where
  site : Site preds
  port : Port args .address
  address : Address cells

def Alias.Valid (conflict : Alias cells args preds) (stage : MixedTail.Result cells args preds)
    (input : Tuple (Val cells) args) : Prop :=
  conflict.site.portAt stage = some conflict.port ∧
    cell input stage.emission.edit.address = conflict.address ∧ cell input conflict.port = conflict.address

def alias? (stage : MixedTail.Result cells args preds) (input : Tuple (Val cells) args) :
    Option (Alias cells args preds) :=
  let address := cell input stage.emission.edit.address
  ((obligations stage).find? fun (_, port) => decide (address = cell input port)).map
    fun (site, port) => ⟨site, port, address⟩

structure Refusal (cells : Nat) (args : List ValueSort) (preds : Predecessors sites) where
  /-- Zero-based index in the original list of admitted cuts. -/
  stageIndex : Nat
  /-- One-based Store version on the preceding retained entry. -/
  version : Nat
  store : Port args .address
  conflict : Alias cells args preds

structure Result (cells : Nat) (args : List ValueSort) (preds : Predecessors sites) where
  /-- The exact prefix recheck, including the preceding artifact, typed entry
  and the original pending stages beginning with the refused stage. -/
  checkedPrefix : Chain.Result cells args preds
  refusal : Option (Refusal cells args preds)

def explain (checkedPrefix : Chain.Result cells args preds) : Option (Refusal cells args preds) := do
  let stage ← checkedPrefix.pending.head?
  let conflict ← alias? stage checkedPrefix.replay.programs.input
  return ⟨checkedPrefix.replay.deleted, stage.version, stage.emission.edit.address, conflict⟩

/-- Diagnose only a refusal of a recorded contract. Structural admission
(including cut and overwrite shape) belongs to the original checked replay. -/
def lower (original : Replay.Result cells args preds) (entry : Memory.Graph args)
    (input : Tuple (Val cells) args) : Result cells args preds :=
  let checkedPrefix := Chain.lower original entry input
  ⟨checkedPrefix, explain checkedPrefix⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Diagnostic
