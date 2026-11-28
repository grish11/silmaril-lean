module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Relocation.Defs

/-! # Opt-in body-local relocation for generated ordered φ splits -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open NamedFlat.Entry.Reverse (Register Registers Lowered numberedInterface lowerCheckedWith)

universe u v

/-- The entry chooses the common packet parameter. Each named block
supplies just its local allocation, independently of all other bodies. -/
structure Relocation.BodyAllocations (blocks : Nat) where
  entry : Registers Register.{u}
  localAt : Fin blocks → Nat → Register.{u}

/-- Solve each body's requests using the same capture and parameter
restrictions and the same finite set of original writes. -/
def Relocation.inferByBody (blocks captures : Nat) (parameter : Register.{u})
    (previous : List Register.{u}) (requests : Relocation.DemandTable.{u}) :
    Option (Relocation.BodyAllocations.{u} blocks) :=
  if requests.blocks.length = blocks then do
    let entry ← Relocation.infer captures parameter previous requests.entry
    let locals ← NamedFlat.tabulate blocks fun i => do
      let needed ← requests.blocks[i.val]?
      let allocation ← Relocation.infer captures parameter previous needed
      return allocation.localAt
    return ⟨entry, locals⟩
  else none

variable {κ V W K : Type (u + 1)} {n : Nat} [DecidableEq V] [DecidableEq W] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} [DecidableEq P.Instr]
  {context : BoundCtx (Ty κ) n} {exits : List (Option K)} {external : Fin exits.length → Ty κ}
  {fields : Option K → List (Register × Ty κ)} {C : Captures V context} {plan : Plan V W K K}
  {a : Admission P (numberedInterface context exits external) fields C}

local notation "Ports" => numberedInterface context exits external

/-- Infer from the actual typed split table and retain its body boundaries. -/
def GeneratedSplit.relocatedByBody (split : GeneratedSplit plan a) (seed : ReverseSeed a) :
    Option (Relocation.BodyAllocations.{u}
      (Versioning.compile (Phi.OrderedExits.lower split.target.source)).blocks.length) := do
  let requests ← Relocation.tableDemands seed.registers.parameter
    (fun i : Fin exits.length => (fields exits[i]).map Prod.fst) split.target.code
  Relocation.inferByBody _ n seed.registers.parameter
    (Relocation.writtenRegisters seed.output.source) requests

/-- Opt in to separate body allocations. Check label injectivity on the
combined internal and external map before running the exact reverse checker. -/
def GeneratedSplit.reverseRelocatedByBody (split : GeneratedSplit plan a) (seed : ReverseSeed a)
    (labels : Fin (Versioning.compile (Phi.OrderedExits.lower split.target.source)).blocks.length → Option K) :
    Option (Lowered Ports fields split.target.code) :=
  if (List.ofFn (SSA.FiniteSum.append labels (fun i : Fin exits.length => exits[i]))).Nodup then
    (split.relocatedByBody seed).bind fun allocation =>
      lowerCheckedWith Ports fields allocation.entry allocation.localAt labels split.target.code
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
