module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Defs
public import Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Theta.Defs

/-! # Checked PEG θ graphs in the scoped MLIR feedback dialect -/

@[expose] public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Scoped

open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open RVSDG.OrderedRuntime.Structured (Data Values)

variable {D : Type} {P : InstructionSet.{0,0} D}

theorem valuePorts_data : (ts : List (Ty D)) → Data (valuePorts ts)
  | [] => .nil
  | _ :: ts => .value (valuePorts_data ts)

/-- The numbered PEG body already has data-only primitive profiles.
Its Boolean-to-selector opcode also uses only data ports. -/
abbrev signature (P : InstructionSet.{0,0} D) : Stateless.Signature (Ty D) where
  pure := Region.Opcode P
  ports
    | .primitive _ => ⟨valuePorts_data _, .value .nil⟩
    | .branch => ⟨.value .nil, .control .nil⟩

abbrev model (m : TotalModel P) : Stateless.Model.{0,0,0} (signature P) where
  value := m.toPEG.Value
  run := Region.evalOpcode m

def encode (m : TotalModel P) {ts : List (Ty D)} (xs : Tuple m.toPEG.Value ts) :
    Tuple (Values (model m).value) (valuePorts ts) :=
  toPorts (F := Values (model m).value) xs

end Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Scoped
