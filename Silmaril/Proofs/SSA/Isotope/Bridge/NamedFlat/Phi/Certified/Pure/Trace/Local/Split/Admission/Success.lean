module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Admission.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split

open Silmaril.Isotope
open Silmaril.Isotope.Bridge
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified (Admission blockCount)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture (close)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)

universe u v
variable {V W K J Base : Type u} {F : Type v} {n : Nat}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
  {plan : Plan V W K J} {source : Graph V K F} {inputs : List V}
  {certificate : Phi.GlobalSSA.Certificate V K}

variable [HasTy F (Ty Base)] [DecidableEq Base]
  {names : Fin n → Option V} {β : BoundCtx (Ty Base) n}
  {blocks : Fin (blockCount source) → Ty Base} {exits : Fin 1 → Ty Base}

theorem generate_eq_of_checks (original : Admission source inputs names β blocks exits)
    (edge : plan.hasEdge source = true) (normalized : (plan.rewrite source).check = true)
    (arrived : Phi.GlobalSSA.check (plan.rewrite source) (inputs.map plan.register)
      (splitCertificate plan source certificate) = true)
    {candidate : ProfileCandidate plan source n Base}
    (profile : profileCandidate plan source names blocks = some candidate) :
    generate plan original certificate =
      (admitProfile plan names β exits candidate certificate
        arrived).bind fun admitted =>
          (close admitted).map fun closed => ⟨candidate.extra, candidate.blocks,
            ⟨original.wellFormed.normalized, edge, normalized, rfl⟩, admitted, closed⟩ := by
  simp only [generate, generateDetailed, edge, normalized, arrived, profile, dite_true]
  generalize admitProfile plan names β exits candidate certificate arrived = admission
  cases admission with
  | none => rfl
  | some admitted =>
    simp only [Option.bind_some]
    cases close admitted <;> rfl

omit [DecidableEq V] in
theorem oldCaptureTypes_sound (candidate : ProfileCandidate plan source n Base)
    {slots : List Nat} (reported : explainTyping plan names β exits candidate = .oldCaptureTypes slots) :
    ∃ graph, NamedFlat.compile (Phi.lower (plan.rewrite source)) [none]
        (extendedNames plan names candidate.extra) = some graph ∧
      NamedFlat.check graph (extendedTypes
        (revisedOldTypes β (oldCaptureRepairs β candidate.movedSlots)) candidate.extra)
          candidate.blocks exits = true ∧
      slots = (oldCaptureRepairs β candidate.movedSlots).map (fun (slot, _) => slot.val) := by
  cases elaborated : NamedFlat.compile (Phi.lower (plan.rewrite source)) [none]
      (extendedNames plan names candidate.extra) with
  | none => simp [explainTyping, elaborated] at reported
  | some graph =>
    refine ⟨graph, rfl, ?_⟩
    simp only [explainTyping, elaborated] at reported
    split at reported
    · rename_i repaired
      exact ⟨(Bool.and_eq_true_iff.mp repaired).2, (Failure.oldCaptureTypes.inj reported).symm⟩
    · cases reported

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split
