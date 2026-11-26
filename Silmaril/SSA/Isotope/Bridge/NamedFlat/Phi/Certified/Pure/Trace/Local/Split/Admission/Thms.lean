module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Admission.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Admission.Arrival
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Admission.Success

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics.Interaction (Primitive)

section Captures

universe u
variable {V W K J Base : Type u} {n : Nat}
  {plan : Plan V W K J} {names : Fin n → Option V} {β : BoundCtx (Ty Base) n}

/-- Every old capture position has the same type in the extended context. -/
@[expose] def originalSlots (β : BoundCtx (Ty Base) n) (extra : List (Option W × Ty Base)) :
    BoundCtx.Renaming β (extendedTypes β extra) :=
  ⟨Fin.castAdd extra.length, fun i => by simp [extendedTypes]⟩

/-- Every retained slot selects the renamed original name. -/
theorem extendedNames_original (extra : List (Option W × Ty Base)) (i : Fin n) :
    extendedNames plan names extra ((originalSlots β extra).toFun i) =
      (names i).map plan.register := by
  simp [extendedNames, originalSlots]

/-- The typed embedding of old slots also preserves their store projections. -/
theorem originalSlots_agree {α : Type u} (extra : List (Option W × Ty Base)) (store : V → Value α)
    (i : Fin n) :
    Certified.captureEnv (extendedNames plan names extra) (plan.renameStore store)
        ((originalSlots β extra).toFun i).val = Certified.captureEnv names store i.val := by
  simp only [Certified.captureEnv, ((originalSlots β extra).toFun i).isLt, i.isLt, dite_true]
  change (extendedNames plan names extra ((originalSlots β extra).toFun i)).elim .unit
    (plan.renameStore store) = (names i).elim .unit store
  simp [extendedNames_original, Plan.renameStore, Function.comp_def]

end Captures

section Success

universe u v
variable {V W K J Base : Type u} {F : Type v} {n : Nat}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
  {plan : Plan V W K J} {source : Graph V K F} {inputs : List V}
  {certificate : Phi.GlobalSSA.Certificate V K}

/-- A checked original table transports to a checked split table for an
existing edge with normalized output. Freshness is supplied by the plan.
The moved φ reads and the original destination claim hold at the new block. -/
theorem splitCertificate_check
    (accepted : Phi.GlobalSSA.check source inputs certificate = true)
    (edge : plan.hasEdge source = true) (normalized : (plan.rewrite source).check = true) :
    Phi.GlobalSSA.check (plan.rewrite source) (inputs.map plan.register)
      (splitCertificate plan source certificate) = true :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split.Arrival.certificate_check
    plan source inputs certificate accepted edge normalized

variable [HasTy F (Ty Base)] [DecidableEq Base]
  {names : Fin n → Option V} {β : BoundCtx (Ty Base) n}
  {blocks : Fin (blockCount source) → Ty Base} {exits : Fin 1 → Ty Base}

omit [DecidableEq V] in
/-- The profile checker is the existing admission API with its arrival
boolean already established. -/
theorem admitProfile_eq (candidate : ProfileCandidate plan source n Base)
    (arrived : Phi.GlobalSSA.check (plan.rewrite source) (inputs.map plan.register)
      (splitCertificate plan source certificate) = true) :
    admitProfile plan names β exits candidate certificate arrived =
      Certified.admit (plan.rewrite source) (inputs.map plan.register)
        (splitCertificate plan source certificate) (extendedNames plan names candidate.extra)
        (extendedTypes β candidate.extra) candidate.blocks exits := by
  simp [admitProfile, Certified.admit, arrived]

/-- Once the old arrival table, edge, normalization and profile reconstruction
are checked, generation is exactly named typed admission followed by pure
closure on that profile. No independent target arrival certificate is needed. -/
theorem generate_eq_of_profile (original : Certified.Admission source inputs names β blocks exits)
    (accepted : Phi.GlobalSSA.check source inputs certificate = true)
    (edge : plan.hasEdge source = true) (normalized : (plan.rewrite source).check = true)
    {candidate : ProfileCandidate plan source n Base}
    (profile : profileCandidate plan source names blocks = some candidate) :
    generate plan original certificate =
      (admitProfile plan names β exits candidate certificate
        (splitCertificate_check accepted edge normalized)).bind fun admitted =>
          (close admitted).map fun closed => ⟨candidate.extra, candidate.blocks,
            ⟨original.wellFormed.normalized, edge, normalized, rfl⟩, admitted, closed⟩ :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split.generate_eq_of_checks original edge normalized
    (splitCertificate_check accepted edge normalized) profile

omit [DecidableEq V] in
/-- For the old-slot diagnostic, changing only the reported slots passes
the checker on the same elaborated graph and generated block packets. -/
theorem oldCaptureTypes_sound (candidate : ProfileCandidate plan source n Base)
    {slots : List Nat} (reported : explainTyping plan names β exits candidate = .oldCaptureTypes slots) :
    ∃ graph, NamedFlat.compile (Phi.lower (plan.rewrite source)) [none]
        (extendedNames plan names candidate.extra) = some graph ∧
      NamedFlat.check graph (extendedTypes
        (revisedOldTypes β (oldCaptureRepairs β candidate.movedSlots)) candidate.extra)
          candidate.blocks exits = true ∧
      slots = (oldCaptureRepairs β candidate.movedSlots).map (fun (slot, _) => slot.val) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split.oldCaptureTypes_sound candidate reported

end Success

section Execution

universe u v
variable {V W K J Base α : Type (u + 1)} {E : Type u → Type u} {F : Type v} {n : Nat}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] [HasTy F (Ty Base)]
  {plan : Plan V W K J} {source : Graph V K F} {inputs : List V}
  {names : Fin n → Option V} {β : BoundCtx (Ty Base) n}
  {blocks : Fin (blockCount source) → Ty Base} {exits : Fin 1 → Ty Base}
  {original : Certified.Admission source inputs names β blocks exits}

/-- The shared source observation law for a generated split, independent
of how the two admitted tables receive their capture records. -/
theorem Generated.sourceObservation_eq (result : Generated plan source inputs names β exits)
    (instr : Primitive E F α) (store : V → Value α) :
    sourceObservation instr source store =
      sourceObservation instr (plan.rewrite source) (plan.renameStore store) :=
  source_eq result.checked instr store

/-- A successful generation result gives equal packed executions even when
the forwarding block requires additional capture slots. The target reads the
same source store through the register equivalence. -/
theorem Generated.packed_eq (result : Generated plan source inputs names β exits)
    (leftClosed : Closed original) (instr : Primitive E F α) (store : V → Value α) :
    packedObservation leftClosed instr store =
      packedObservation result.closed instr (plan.renameStore store) := by
  rw [packedObservation_eq_sourceObservation, packedObservation_eq_sourceObservation]
  exact result.sourceObservation_eq instr store

end Execution

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split
