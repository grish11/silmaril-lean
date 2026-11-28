module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Admission.Defs

/-! # Capture liveness at the ordered φ split interface -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v
variable {κ V W Reg K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {I : NamedFlat.Entry.Interface κ Reg (Option K)}
  {fields : Option K → List (Reg × Ty κ)} {C : Captures V I.context}

/-- The actual original lexical entry has a free version-zero read of this slot. -/
def Admission.entryUsesSlot (a : Admission P I fields C) (slot : Fin I.slots) : Prop :=
  (C.names slot, 0) ∈ (Versioning.compile (Phi.OrderedExits.lower a.source)).entry.toRegion.fv

instance (a : Admission P I fields C) (slot : Fin I.slots) : Decidable (a.entryUsesSlot slot) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- Positions whose version-zero reads were introduced by the moved operand
column and whose names are already in the common typed input interface. -/
def Admission.movedCaptureSlots [DecidableEq W] (a : Admission P I fields C) (plan : Plan V W K K) :
    List (Fin I.slots) :=
  ((a.splitProfile plan).map (fun profile => profile.movedSlots.map Prod.fst)).getD []

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
