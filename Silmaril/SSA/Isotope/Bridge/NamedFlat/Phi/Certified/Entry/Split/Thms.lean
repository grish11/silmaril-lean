module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Split.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Admission.Thms

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan Checked)
open LambdaSSA (Region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Elgot.ITree (TraceLE)

universe u v

variable {κ V W K J : Type (u + 1)} {n : Nat} {β : BoundCtx (Ty κ) n}
  {I : Captures V β} {D : Fin 1 → Ty κ}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] [AtomValues κ]
  {P : FlatInstitution.Signature.{u, v} κ} {Events : Type u → Type u}

local notation "C" => AtomValues.carrier (κ := κ)
local notation "Record" => Ty.denote C (Region.packedInputType β.toList)

/-- Splitting an edge changes neither the request/reply tree nor its encoded
exit when both admissions take the same record under the renamed fields. -/
theorem split_observe_eq (plan : Plan V W K J) (original : Admitted P I K D)
    (split : Admitted P (I.rename plan.register) J D) (checked : Checked plan original.source split.source)
    (M : Model (κ := κ) Events P.Instr) (record : Record) :
    original.observe M record = split.observe M record := by
  simp only [Admitted.observe, Captures.store_rename]
  exact PureCapture.Local.Split.source_eq checked M.raw (I.store record)

/-- The directed comparisons in both directions between an original graph
and its checked split are satisfied in the existing typed-entry room. -/
theorem split_satisfies (plan : Plan V W K J) (original : Admitted P I K D)
    (split : Admitted P (I.rename plan.register) J D) (checked : Checked plan original.source split.source)
    (M : Model (κ := κ) Events P.Instr) :
    EntryInstitution.Satisfies Events M (toFlat (original, split)) ∧
      EntryInstitution.Satisfies Events M (toFlat (split, original)) := by
  simp only [toFlat_satisfies_iff, Satisfies]
  exact ⟨fun record => split_observe_eq plan original split checked M record ▸ TraceLE.refl _,
    fun record => split_observe_eq plan original split checked M record ▸ TraceLE.refl _⟩

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
