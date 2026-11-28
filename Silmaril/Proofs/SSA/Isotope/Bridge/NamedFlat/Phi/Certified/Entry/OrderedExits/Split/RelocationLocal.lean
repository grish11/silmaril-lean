module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Relocation.Local.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Relocation.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.RelocationLocal

open Silmaril.Isotope
open Silmaril.Isotope.Bridge
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry (Captures)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open NamedFlat.Entry.Reverse (Register Lowered numberedInterface withLiveOut lowerWith lowerCheckedWith_emitted)

universe u v

theorem infer_valid (blocks captures : Nat) (parameter : Register.{u})
    (previous : List Register.{u}) (requests : Relocation.DemandTable.{u})
    {allocation : Relocation.BodyAllocations.{u} blocks}
    (inferred : Relocation.inferByBody blocks captures parameter previous requests = some allocation) :
    Relocation.Valid captures parameter previous requests.entry allocation.entry ∧
      ∀ i : Fin blocks, ∃ needed, requests.blocks[i.val]? = some needed ∧
        Relocation.Valid captures parameter previous needed ⟨allocation.entry.parameter, allocation.localAt i⟩ := by
  unfold Relocation.inferByBody at inferred
  split at inferred
  next =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at inferred
    obtain ⟨entry, entryEq, rows, rowsEq, rfl⟩ := inferred
    have entryValid := Relocation.infer_valid captures parameter previous _ entryEq
    refine ⟨entryValid, fun i => ?_⟩
    have row := NamedFlat.tabulate_at rowsEq i
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at row
    obtain ⟨needed, found, registers, inferred, sameLocals⟩ := row
    have valid := Relocation.infer_valid captures parameter previous _ inferred
    have sameParameter := entryValid.sameParameter.trans valid.sameParameter.symm
    obtain ⟨param, locals⟩ := registers
    cases sameLocals
    cases sameParameter
    exact ⟨needed, found, valid⟩
  next => contradiction

variable {κ V W K : Type (u + 1)} {n : Nat} [DecidableEq V] [DecidableEq W] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} [DecidableEq P.Instr]
  {context : BoundCtx (Ty κ) n} {exits : List (Option K)} {external : Fin exits.length → Ty κ}
  {fields : Option K → List (Register × Ty κ)} {C : Captures V context} {plan : Plan V W K K}
  {a : Admission P (numberedInterface context exits external) fields C}

local notation "Ports" => numberedInterface context exits external

theorem reverse_spec (split : GeneratedSplit plan a) (seed : ReverseSeed a)
    (labels : Fin (Versioning.compile (Phi.OrderedExits.lower split.target.source)).blocks.length → Option K) {output : Lowered Ports fields split.target.code}
    (accepted : split.reverseRelocatedByBody seed labels = some output) :
    Function.Injective (SSA.FiniteSum.append labels (fun i : Fin exits.length => exits[i])) ∧
      ∃ allocation, split.relocatedByBody seed = some allocation ∧
        lowerWith allocation.entry allocation.localAt (Ports).names labels (fun i : Fin exits.length => exits[i])
          split.target.code = some output.source ∧
        NamedFlat.elaborateAt (withLiveOut fields output.source) exits (Ports).names _ output.count =
          some split.target.code := by
  unfold GeneratedSplit.reverseRelocatedByBody at accepted
  split at accepted
  next unique =>
    obtain ⟨allocation, inferred, checked⟩ := Option.bind_eq_some_iff.mp accepted
    exact ⟨List.nodup_ofFn.mp unique, allocation, inferred, lowerCheckedWith_emitted checked, output.readback⟩
  next => contradiction

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.RelocationLocal
