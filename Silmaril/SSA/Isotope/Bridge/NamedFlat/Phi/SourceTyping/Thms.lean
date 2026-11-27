module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.SourceTyping.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.SourceTyping

/-! # The typed packet of a lowered and versioned edge

A certified jump of a φ graph is followed through the lowering and the
versioning, and the value that the versioned jump carries is typed.

On a jump to a block the lowering sends the φ operands of the target that
this predecessor supplies, packed in the order of the rows, and the
versioning pairs them with the record of the target, in the order of its
layout. The pair has the computed packet type of the target. The record
holds source registers only: the packet register is the parameter of
every lowered block and is left out of every layout.

On a jump to a label that is not a block there is no record, and the
payload has the declared type of the label.

Both hold for any typing of the versioned names in which the current
version of every source register has its declared type. That is the
state that the versioning maintains along a body; it is a hypothesis
here, and it is not proved here that the versioning maintains it.

What remains for the typed elaboration is `Task.certifiedChecks`. It
needs three things that are not proved: that the versioned bodies keep
the current versions at their declared types, binder by binder; that a
versioned block, which takes its packet apart into the φ operands and the
record and unpacks both, restores that state from the computed packet
type; and that the elaboration to positional terms turns the named typing
into the typing check of the elaborated graph. Given the open statement,
the typed elaboration returns the elaborated graph at the computed packet
types; with the theorem on closed tables no elaboration is assumed.
-/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceTyping

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG (Term)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Block Row)

universe u v

variable {Base V K : Type u} {F : Type v}

/-- A value read at current versions has the type of the value, when the
current version of each register it reads has the type of the register. -/
theorem valueType_rn {W : Type u} (types : W → Ty Base) (versioned : W × Nat → Ty Base)
    (cur : W → Nat) (value : Val W)
    (current : ∀ z ∈ value.fvList, versioned (z, cur z) = types z) :
    valueType versioned (Version.rn cur value) = valueType types value :=
  valueType_rn_proof types versioned cur value current

/-- The record of a list of registers, read at current versions, has the
record type of the list. -/
theorem valueType_record {W : Type u} (types : W → Ty Base) (versioned : W × Nat → Ty Base)
    (cur : W → Nat) (registers : List W)
    (current : ∀ y ∈ registers, versioned (y, cur y) = types y) :
    valueType versioned (Version.pack cur registers) = recordType types registers :=
  valueType_record_proof types versioned cur registers current

/-- The packed φ operands of an edge have the type of the rows, when each
operand has the type of its destination. -/
theorem valueType_args [DecidableEq K] (types : V → Ty Base) (pred : Option K)
    (rows : List (Row V K))
    (operands : ∀ row ∈ rows, valueType types (row.operand pred) = types row.dst) :
    valueType (lifted types) (Phi.pack (Phi.arguments pred rows)) = argsType types rows :=
  valueType_args_proof types pred rows operands

variable [DecidableEq V] [DecidableEq K]

/-- The record that the versioning carries to a block of the lowering is
the layout of the lowered block. -/
theorem destinations_lower (graph : Graph V K F) (key : K) :
    Versioning.destinations (Phi.OrderedExits.lower graph) (some key) =
      (graph.blocks.lookup key).map fun block =>
        Versioning.slots (Phi.OrderedExits.lower graph)
          (Phi.OrderedExits.lowerBlock graph key block) :=
  destinations_some_proof graph key

/-- The record of a lowered block holds source registers only. -/
theorem slots_some (graph : Graph V K F) (key : K) (block : Block V K F) :
    ∀ y ∈ Versioning.slots (Phi.OrderedExits.lower graph)
      (Phi.OrderedExits.lowerBlock graph key block), ∃ r, y = some r :=
  slots_some_proof graph key block

variable [DecidableEq Base] [HasTy F (Ty Base)]

/-- A certified jump to a block, lowered and versioned, carries a packet
of the computed packet type of the block, when the current version of
every source register has its declared type. -/
theorem edge_packet (graph : Graph V K F) (types : V → Ty Base) (exitType : Option K → Ty Base)
    (pred : Option K) (key : K) (block : Block V K F) (value : Val V)
    (found : graph.blocks.lookup key = some block)
    (typed : termTyped graph types exitType pred (.br (some key) value) = true)
    (live : List (Option V)) (cur : Option V → Nat) (depth : Nat)
    (versioned : Option V × Nat → Ty Base)
    (current : ∀ register, versioned (some register, cur (some register)) = types register) :
    ∃ payload, Version.version (Versioning.destinations (Phi.OrderedExits.lower graph)) live cur
        depth (Phi.liftTerm (Phi.OrderedExits.branchValue graph pred)
          (.br (some key) value : Term V (Option K) F)).toRegion = .br (some key) payload ∧
      valueType versioned payload = packetType graph types key block :=
  edge_packet_proof graph types exitType pred key block value found typed live cur depth versioned
    current

/-- A certified jump to a label that is not a block, lowered and
versioned, carries a payload of the declared type of the label, and no
record. -/
theorem exit_payload (graph : Graph V K F) (types : V → Ty Base) (exitType : Option K → Ty Base)
    (pred target : Option K) (value : Val V)
    (absent : Phi.OrderedExits.lookup graph target = none)
    (typed : termTyped graph types exitType pred (.br target value) = true)
    (live : List (Option V)) (cur : Option V → Nat) (depth : Nat)
    (versioned : Option V × Nat → Ty Base)
    (current : ∀ register, versioned (some register, cur (some register)) = types register) :
    ∃ payload, Version.version (Versioning.destinations (Phi.OrderedExits.lower graph)) live cur
        depth (Phi.liftTerm (Phi.OrderedExits.branchValue graph pred)
          (.br target value : Term V (Option K) F)).toRegion = .br target payload ∧
      valueType versioned payload = exitType target :=
  exit_payload_proof graph types exitType pred target value absent typed live cur depth versioned
    current

/-- Given the open statement, the typed elaboration of the lowering of a
certified φ graph returns the elaborated graph at the computed packet
types. -/
theorem compileTyped_of_certified (open_ : Task.certifiedChecks Base V K F) (graph : Graph V K F)
    (exits : List (Option K)) (types : V → Ty Base) (exitType : Option K → Ty Base) {n : Nat}
    (captures : Fin n → Option V) (captureTypes : BoundCtx (Ty Base) n)
    {target : LambdaSSA.FiniteCFG F (Versioning.compile (Phi.OrderedExits.lower graph)).blocks.length
      exits.length n}
    (certificate : certified graph types exitType = true)
    (declared : ∀ i, captureTypes.get i = lifted types (captures i))
    (elaborated : NamedFlat.compile (Phi.OrderedExits.lower graph) exits captures = some target) :
    ∃ result, compileTyped (Phi.OrderedExits.lower graph) exits captures captureTypes
        (internal graph types) (external exits exitType) = some result ∧ result.val = target :=
  compileTyped_of_check (Phi.OrderedExits.lower graph) exits captures captureTypes
    (internal graph types) (external exits exitType) elaborated
    (open_ graph exits types exitType captures captureTypes target certificate declared elaborated)

/-- Given the open statement, the typed elaboration succeeds for the
normalized graph of a closed forwarding table, from checks on the φ
graphs only: the table is closed, the graph is in the fragment, the
normalized graph is certified, and the captures cover the declared inputs
at their declared types. -/
theorem compileTyped_of_closed
    (open_ : Task.certifiedChecks Base (Phi.Forward.Name V K) K F) (graph : Graph V K F)
    (table : Phi.Forward.Table V K) (exits : List (Option K)) (inputs : List V)
    (types : Phi.Forward.Name V K → Ty Base) (exitType : Option K → Ty Base) {n : Nat}
    (captures : Fin n → Option (Phi.Forward.Name V K)) (captureTypes : BoundCtx (Ty Base) n)
    (isClosed : Phi.Forward.closed graph table exits inputs = true)
    (fragment : NamedFlat.Phi.plain graph = true)
    (covered : ∀ z ∈ inputs, ∃ i, captures i = some (Sum.inl z))
    (certificate : certified (Phi.Forward.forward graph table) types exitType = true)
    (declared : ∀ i, captureTypes.get i = lifted types (captures i)) :
    (compileTyped (Phi.OrderedExits.lower (Phi.Forward.forward graph table)) exits captures
      captureTypes (internal (Phi.Forward.forward graph table) types)
      (external exits exitType)).isSome = true := by
  obtain ⟨target, elaborated⟩ := Option.isSome_iff_exists.mp
    (NamedFlat.Phi.compile_of_closed graph table exits inputs captures isClosed fragment covered)
  obtain ⟨result, typed, _⟩ := compileTyped_of_certified open_ (Phi.Forward.forward graph table)
    exits types exitType captures captureTypes certificate declared elaborated
  rw [typed]
  rfl

end Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceTyping
