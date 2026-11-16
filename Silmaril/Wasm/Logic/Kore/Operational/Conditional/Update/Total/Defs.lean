module

public import Silmaril.Wasm.Logic.Kore.Operational.Conditional.Update.Thms
public import Silmaril.Logic.CTL.Derived.Thms
public import Silmaril.Logic.CTL.Mu.Thms
public import Silmaril.Logic.Matching.FixedPoint.Modal.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core

/-- One atom records the actual native target relation, without abstracting the
native state space or changing the step relation. -/
abbrev targetSignature : Silmaril.Logic.CTL.Signature := ⟨Unit⟩

def predicateModel {H : Type} (P : Silmaril.Wasm.Numerics.Profile)
    (host : HostSemantics H) (initial : Core.Config H) (Q : Core.Config H → Prop) :
    Silmaril.Logic.CTL.Model targetSignature :=
  ⟨{ World := Core.Config H, accessible := Core.Step P host,
     valuation := fun _ => Q, point := initial }⟩

/-- Strong CTL AF includes infinite paths and finite paths ending in deadlock. -/
abbrev eventuallyTarget : Silmaril.Logic.CTL.Formula targetSignature := .af (.atom ())

end Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.NativeTotal
