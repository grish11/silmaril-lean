module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Admission.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Straight.Thms

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open NamedFlat.Entry.Record (Input)
open NamedFlat.Entry.Reverse (Register Lowered numberedInterface)
open NamedFlat.Entry.Reverse.Straight (admitWithCaptures keepsEntryCaptures checks)

universe u v
variable {κ V W K : Type (u + 1)} {n : Nat}
  [DecidableEq κ] [DecidableEq V] [DecidableEq W] [DecidableEq K] [AtomValues κ]
  {P : FlatInstitution.Signature.{u, v} κ} {context : BoundCtx (Ty κ) n}
  {exits : List (Option K)} {external : Fin exits.length → Ty κ}
  {fields : Option K → List (Register × Ty κ)} {C : Captures V context} {Events : Type u → Type u}
  {plan : Plan V W K K}

local notation "Ports" => numberedInterface context exits external
local notation "Atoms" => AtomValues.carrier (κ := κ)

variable {a : Admission P (numberedInterface context exits external) fields C}

/-- Compose the checked φ split with source-local typed re-admission of
both actual reverse outputs. Each side can save a different ordered list
of unchanged numbered slots, uniformly at all its own destinations. -/
theorem GeneratedSplit.roundTrip_eq_of_uniformReadback (split : GeneratedSplit plan a)
    (left : Lowered Ports fields a.code) (right : Lowered Ports fields split.target.code)
    (leftSlots rightSlots : List (Fin n))
    (leftLayout : ∀ i, left.savedRegisters i = leftSlots.map (fun j => (⟨j.val⟩ : Register)))
    (rightLayout : ∀ i, right.savedRegisters i = rightSlots.map (fun j => (⟨j.val⟩ : Register)))
    (leftKept : keepsEntryCaptures left leftSlots = true)
    (rightKept : keepsEntryCaptures right rightSlots = true)
    (leftChecked : checks left a.internal = true) (rightChecked : checks right split.target.internal = true)
    (M : Model (κ := κ) Events P.Instr) (record : Input context) (ambient : Env (Sigma Atoms)) :
    let lhs := admitWithCaptures left a.internal leftSlots leftLayout leftKept leftChecked
    let rhs := admitWithCaptures right split.target.internal rightSlots rightLayout rightKept rightChecked
    region M.raw (extend ambient (encodeValue Atoms _ record)) lhs.program.code =
      region M.raw (extend ambient (encodeValue Atoms _ record)) rhs.program.code :=
  split.roundTrip_eq left right
    (admitWithCaptures left a.internal leftSlots leftLayout leftKept leftChecked)
    (admitWithCaptures right split.target.internal rightSlots rightLayout rightKept rightChecked) M record ambient

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
