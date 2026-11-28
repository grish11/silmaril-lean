module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Relocation.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.ReverseAcceptance.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Relocation

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open NamedFlat.Entry.Reverse (Register Registers Lowered numberedInterface lower lowerChecked withLiveOut)

universe u v

/-- Successful inference preserves every requested physical name and keeps
all local depths distinct and outside the input and parameter registers.
Unconstrained depths also avoid registers written by the original output. -/
theorem Relocation.infer_valid (captures : Nat) (parameter : Register.{u}) (previous : List Register.{u})
    (needed : List Relocation.Demand.{u}) {allocation : Registers Register.{u}}
    (found : Relocation.infer captures parameter previous needed = some allocation) :
    Relocation.Valid captures parameter previous needed allocation :=
  Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Relocation.infer_valid
    captures parameter previous needed found

/-- At a single exit, matching the recovered requests is exactly equality
with the ordered physical register reads after resolving symbolic binders.
The field list also checks direct-read shape, arity, and fixed names. -/
theorem Relocation.readDemands_iff {allocation : Registers Register.{u}} {parameter : Register.{u}}
    (fixed : allocation.parameter = parameter) {value : Val Relocation.Origin} {fields : List Register.{u}} :
    Relocation.renameValue allocation value = LiveOut.reads fields ↔
      ∃ needed, Relocation.readDemands parameter value fields = some needed ∧
        ∀ r ∈ needed, allocation.localAt r.1 = r.2 :=
  Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Relocation.readDemands_iff fixed

/-- Every valid graph-wide allocation induces these finite constraints. -/
theorem Relocation.Valid.constraints {captures : Nat} {parameter : Register.{u}} {prior : List Register.{u}}
    {needed : List Relocation.Demand.{u}} {allocation : Registers Register.{u}}
    (valid : Relocation.Valid captures parameter prior needed allocation) :
    Relocation.Constraints captures parameter needed :=
  Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Relocation.constraints_of_valid valid

/-- The finite constraints suffice for the deterministic completion, with
fresh unrequested locals above the original writes and requested names. -/
theorem Relocation.infer_of_constraints {captures : Nat} {parameter : Register.{u}} (prior : List Register.{u})
    {needed : List Relocation.Demand.{u}} (constraints : Relocation.Constraints captures parameter needed) :
    infer captures parameter prior needed = some (complete captures parameter prior needed) :=
  Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Relocation.infer_of_constraints
    prior constraints

/-- The allocator succeeds exactly when a policy-respecting allocation exists. -/
theorem Relocation.infer_isSome_iff_valid (captures : Nat) (parameter : Register.{u}) (prior : List Register.{u})
    (needed : List Relocation.Demand.{u}) :
    (infer captures parameter prior needed).isSome = true ↔
      ∃ allocation, Valid captures parameter prior needed allocation :=
  ⟨fun ok => (Option.isSome_iff_exists.mp ok).imp fun reg h => infer_valid captures parameter prior needed h,
    fun ⟨_, valid⟩ => by rw [infer_of_constraints prior valid.constraints]; rfl⟩

/-- A finite characterization of the independent allocation problem. -/
theorem Relocation.constraints_iff_valid (captures : Nat) (parameter : Register.{u}) (prior : List Register.{u})
    (needed : List Relocation.Demand.{u}) :
    Constraints captures parameter needed ↔ ∃ allocation, Valid captures parameter prior needed allocation :=
  ⟨fun c => ⟨_, infer_valid captures parameter prior needed (infer_of_constraints prior c)⟩,
    fun ⟨_, valid⟩ => valid.constraints⟩

variable {κ V W K : Type (u + 1)} {n : Nat} [DecidableEq V] [DecidableEq W] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} [DecidableEq P.Instr]
  {context : BoundCtx (Ty κ) n} {exits : List (Option K)} {external : Fin exits.length → Ty κ}
  {fields : Option K → List (Register × Ty κ)} {C : Captures V context} {plan : Plan V W K K}
  {a : Admission P (numberedInterface context exits external) fields C}

local notation "Ports" => numberedInterface context exits external

/-- The recovered allocation satisfies the ordered requests of the actual
admitted split table, including repeated requests across different blocks. -/
theorem GeneratedSplit.relocatedRegisters_valid (split : GeneratedSplit plan a) (seed : ReverseSeed a)
    {allocation : Registers Register} (found : split.relocatedRegisters seed = some allocation) :
    ∃ needed, split.relocationDemands seed = some needed ∧
      Relocation.Valid n seed.registers.parameter (Relocation.writtenRegisters seed.output.source) needed allocation := by
  obtain ⟨needed, requests, solved⟩ := Option.bind_eq_some_iff.mp found
  exact ⟨needed, requests, Relocation.infer_valid _ _ _ _ solved⟩

/-- When the symbolic pass parses the generated table, allocation succeeds
exactly for the finite constraints extracted from its ordered reads. -/
theorem GeneratedSplit.relocatedRegisters_isSome_iff (split : GeneratedSplit plan a) (seed : ReverseSeed a)
    {needed : List Relocation.Demand.{u}} (requests : split.relocationDemands seed = some needed) :
    (split.relocatedRegisters seed).isSome = true ↔
      Relocation.Constraints n seed.registers.parameter needed := by
  rw [GeneratedSplit.relocatedRegisters, requests, Option.bind_some,
    Relocation.infer_isSome_iff_valid, Relocation.constraints_iff_valid]

/-- The inferred reverse result is the actual emission at the recovered
allocation. Exact readback includes the declared field order at each exit. -/
theorem GeneratedSplit.reverseRelocated_spec (split : GeneratedSplit plan a) (seed : ReverseSeed a)
    (labels : Fin (Versioning.compile (Phi.OrderedExits.lower split.target.source)).blocks.length → Option K)
    {output : Lowered Ports fields split.target.code}
    (accepted : split.reverseRelocated seed labels = some output) :
    ∃ allocation, split.relocatedRegisters seed = some allocation ∧
      lower allocation (Ports).names labels (fun i => exits[i]) split.target.code = some output.source ∧
      NamedFlat.elaborateAt (withLiveOut fields output.source) exits (Ports).names _ output.count =
        some split.target.code := by
  obtain ⟨allocation, inferred, checked⟩ := Option.bind_eq_some_iff.mp accepted
  exact ⟨allocation, inferred, NamedFlat.Entry.Reverse.lowerChecked_emitted checked, output.readback⟩

/-- Given the inferred allocation and successful RTL emission, only the
exact readback equation remains. In particular, the allocation constraints
do not replace the checks on the supplied block labels. -/
theorem GeneratedSplit.reverseRelocated_iff_readback (split : GeneratedSplit plan a) (seed : ReverseSeed a)
    (labels : Fin (Versioning.compile (Phi.OrderedExits.lower split.target.source)).blocks.length → Option K)
    {allocation : Registers Register} {source : CFG Register (Option K) P.Instr}
    (inferred : split.relocatedRegisters seed = some allocation)
    (emitted : lower allocation (Ports).names labels (fun i => exits[i]) split.target.code = some source) :
    (split.reverseRelocated seed labels).isSome = true ↔
      NamedFlat.elaborateAt (withLiveOut fields source) exits (Ports).names _
        (NamedFlat.Entry.Reverse.lower_attached_count fields emitted) = some split.target.code := by
  rw [GeneratedSplit.reverseRelocated, inferred, Option.bind_some]
  exact split.reverseChecked_iff_readback allocation labels emitted

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
