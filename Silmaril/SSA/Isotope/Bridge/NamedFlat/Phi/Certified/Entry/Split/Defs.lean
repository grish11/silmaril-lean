module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Admission.Defs

/-! # A generated split at the unchanged supplied record type -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open PureCapture.Local.Split (Generated extendedNames extendedTypes)

universe u v

variable {κ V W K J : Type (u + 1)} {n : Nat} {β : BoundCtx (Ty κ) n}
  {I : Captures V β} {D : Fin 1 → Ty κ}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
  {P : FlatInstitution.Signature.{u, v} κ} {source : Graph V K P.Instr} {inputs : List V}

/-- A generated split with no extra capture fields already supplies a checked
admission at the renamed original interface. -/
def Admitted.ofGenerated (plan : Plan V W K J) (result : Generated plan source inputs I.names β D)
    (sameRecord : result.extra = []) : Admitted P (I.rename plan.register) J D :=
  ⟨plan.rewrite source, inputs.map plan.register, result.blocks, by
    have names : extendedNames plan I.names ([] : List (Option W × Ty κ)) = (I.rename plan.register).names :=
      funext fun i => by
        simp [extendedNames, Captures.rename, Fin.addCases]
        rfl
    have types : extendedTypes β ([] : List (Option W × Ty κ)) = β := by
      apply (BoundCtx.finEquiv (Ty κ) n).injective
      funext i
      change (extendedTypes β ([] : List (Option W × Ty κ))).get i = β.get i
      simp [extendedTypes, BoundCtx.get_ofFin, Fin.addCases]
      rfl
    cases result with
    | mk extra blocks checked admitted closed =>
      change extra = [] at sameRecord
      subst extra
      simpa only [names, types] using admitted⟩

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
