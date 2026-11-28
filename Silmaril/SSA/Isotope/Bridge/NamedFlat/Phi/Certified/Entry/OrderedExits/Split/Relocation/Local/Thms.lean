module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Relocation.Local.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Relocation.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Execution.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.RelocationLocal

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open NamedFlat.Entry.Reverse (Register Lowered numberedInterface withLiveOut lowerWith)

universe u v

/-- Inferred locals respect the original policy within each body, with
the same parameter and protected capture range throughout the table. -/
theorem Relocation.inferByBody_valid (blocks captures : Nat) (parameter : Register.{u})
    (previous : List Register.{u}) (requests : Relocation.DemandTable.{u})
    {allocation : Relocation.BodyAllocations.{u} blocks}
    (inferred : Relocation.inferByBody blocks captures parameter previous requests = some allocation) :
    Relocation.Valid captures parameter previous requests.entry allocation.entry ∧
      ∀ i : Fin blocks, ∃ needed, requests.blocks[i.val]? = some needed ∧
        Relocation.Valid captures parameter previous needed ⟨allocation.entry.parameter, allocation.localAt i⟩ :=
  Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.RelocationLocal.infer_valid
    blocks captures parameter previous requests inferred

variable {κ V W K : Type (u + 1)} {n : Nat} [DecidableEq V] [DecidableEq W] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} [DecidableEq P.Instr]
  {context : BoundCtx (Ty κ) n} {exits : List (Option K)} {external : Fin exits.length → Ty κ}
  {fields : Option K → List (Register × Ty κ)} {C : Captures V context} {plan : Plan V W K K}
  {a : Admission P (numberedInterface context exits external) fields C}

local notation "Ports" => numberedInterface context exits external

/-- Acceptance certifies distinct labels, actual body-local emission, and
exact readback to the same typed table with its ordered exit fields. -/
theorem GeneratedSplit.reverseRelocatedByBody_spec (split : GeneratedSplit plan a) (seed : ReverseSeed a)
    (labels : Fin (Versioning.compile (Phi.OrderedExits.lower split.target.source)).blocks.length → Option K) {output : Lowered Ports fields split.target.code}
    (accepted : split.reverseRelocatedByBody seed labels = some output) :
    Function.Injective (SSA.FiniteSum.append labels (fun i : Fin exits.length => exits[i])) ∧
      ∃ allocation, split.relocatedByBody seed = some allocation ∧
        lowerWith allocation.entry allocation.localAt (Ports).names labels (fun i : Fin exits.length => exits[i])
          split.target.code = some output.source ∧
        NamedFlat.elaborateAt (withLiveOut fields output.source) exits (Ports).names _ output.count =
          some split.target.code :=
  Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.RelocationLocal.reverse_spec
    split seed labels accepted

section Execution

open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open Silmaril.Isotope.Semantics (encodeValue)
open NamedFlat.Entry.Record (Input)
open NamedFlat.Entry.Reverse (observeAttached)

variable [AtomValues κ] {Events : Type u → Type u}

/-- The original independent φ graph agrees with the attached RTL emitted
for its checked split and with that split's packed LambdaSSA execution. -/
theorem GeneratedSplit.bodyLocal_commutes (split : GeneratedSplit plan a) (seed : ReverseSeed a)
    (labels : Fin _ → Option K) {output : Lowered Ports fields split.target.code}
    (accepted : split.reverseRelocatedByBody seed labels = some output)
    (M : Model (κ := κ) Events P.Instr) (record : Input context)
    (ambient : Env (Sigma (AtomValues.carrier (κ := κ)))) :
    Function.Injective (SSA.FiniteSum.append labels (fun i : Fin exits.length => exits[i])) ∧
      a.observe M record = observeAttached M Ports fields output.source record ∧
      a.observe M record =
        region M.raw (extend ambient (encodeValue _ _ record)) (Program.ofCFGEntry split.target.typed).code :=
  let same := split.observe_eq M record
  ⟨(split.reverseRelocatedByBody_spec seed labels accepted).1,
    same.trans (split.target.observe_attached output M record),
    same.trans (split.target.observe_packed M record ambient)⟩

end Execution

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
