module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.CaptureLiveness.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Admission.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.CaptureLiveness

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open NamedFlat.Entry.Record (Input field)

universe u v
variable {κ V W Reg K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {I : NamedFlat.Entry.Interface κ Reg (Option K)}
  {fields : Option K → List (Reg × Ty κ)} {C : Captures V I.context}

theorem Admission.movedCaptureSlot_unused [DecidableEq W] (a : Admission P I fields C)
    (plan : Plan V W K K) {slot : Fin I.slots} (member : slot ∈ a.movedCaptureSlots plan) :
    ¬ a.entryUsesSlot slot :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.movedCaptureSlot_unused a plan member

variable [AtomValues κ] {Events : Type u → Type u}

local notation "Atoms" => AtomValues.carrier (κ := κ)

/-- Agreement on the actual lexical entry's free input slots suffices for
the same ordered φ observation. Subsequent blocks read only their packets. -/
theorem Admission.observe_eq_of_entryAgreement (a : Admission P I fields C)
    (M : Model (κ := κ) Events P.Instr) (left right : Input I.context)
    (agrees : ∀ i, a.entryUsesSlot i → field I.context left i = field I.context right i) :
    a.observe M left = a.observe M right :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.observe_eq_of_entryAgreement
    a M left right agrees

variable [DecidableEq W] {plan : Plan V W K K} {a : Admission P I fields C}

/-- Vary all generated operand capture slots together at the common typed
record. The accepted split still has the same independent φ observation,
including every visible continuation and the final exit tag. -/
theorem GeneratedSplit.observe_eq_of_movedCaptures (split : GeneratedSplit plan a)
    (M : Model (κ := κ) Events P.Instr) (left right : Input I.context)
    (agrees : ∀ i, i ∉ a.movedCaptureSlots plan → field I.context left i = field I.context right i) :
    split.target.observe M left = split.target.observe M right :=
  (split.observe_eq M left).symm.trans
    ((a.observe_eq_of_entryAgreement M left right
      (fun i used => agrees i (fun member => a.movedCaptureSlot_unused plan member used))).trans
        (split.observe_eq M right))

/-- The actual typed packed split table is insensitive to the same slots. -/
theorem GeneratedSplit.packed_eq_of_movedCaptures (split : GeneratedSplit plan a)
    (M : Model (κ := κ) Events P.Instr) (left right : Input I.context) (ambient : Env (Sigma Atoms))
    (agrees : ∀ i, i ∉ a.movedCaptureSlots plan → field I.context left i = field I.context right i) :
    region M.raw (extend ambient (encodeValue Atoms _ left)) (Program.ofCFGEntry split.target.typed).code =
      region M.raw (extend ambient (encodeValue Atoms _ right)) (Program.ofCFGEntry split.target.typed).code :=
  (split.target.observe_packed M left ambient).symm.trans
    ((split.observe_eq_of_movedCaptures M left right agrees).trans (split.target.observe_packed M right ambient))

variable [DecidableEq Reg]

/-- An accepted reverse readback has the same independence in the actual
mutable execution and its ordered exit live-outs. -/
theorem GeneratedSplit.reverse_eq_of_movedCaptures (split : GeneratedSplit plan a)
    (lowered : NamedFlat.Entry.Reverse.Lowered I fields split.target.code)
    (M : Model (κ := κ) Events P.Instr) (left right : Input I.context)
    (agrees : ∀ i, i ∉ a.movedCaptureSlots plan → field I.context left i = field I.context right i) :
    NamedFlat.Entry.LiveOut.observe M I fields lowered.source left =
      NamedFlat.Entry.LiveOut.observe M I fields lowered.source right :=
  (split.target.observe_reverse lowered M left).symm.trans
    ((split.observe_eq_of_movedCaptures M left right agrees).trans (split.target.observe_reverse lowered M right))

/-- A successful typed re-admission preserves the same independence. -/
theorem GeneratedSplit.roundTrip_eq_of_movedCaptures (split : GeneratedSplit plan a)
    (lowered : NamedFlat.Entry.Reverse.Lowered I fields split.target.code)
    (recompiled : NamedFlat.Entry.LiveOut.Admission P I fields lowered.source)
    (M : Model (κ := κ) Events P.Instr) (left right : Input I.context) (ambient : Env (Sigma Atoms))
    (agrees : ∀ i, i ∉ a.movedCaptureSlots plan → field I.context left i = field I.context right i) :
    region M.raw (extend ambient (encodeValue Atoms _ left)) recompiled.program.code =
      region M.raw (extend ambient (encodeValue Atoms _ right)) recompiled.program.code :=
  (split.target.observe_roundTrip lowered recompiled M left ambient).symm.trans
    ((split.observe_eq_of_movedCaptures M left right agrees).trans
      (split.target.observe_roundTrip lowered recompiled M right ambient))

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
