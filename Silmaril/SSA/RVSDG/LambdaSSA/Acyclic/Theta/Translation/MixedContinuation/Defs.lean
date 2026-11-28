module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Executable.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Splice.Defs

/-! # Attach a public ordered translation after a checked mixed region -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation

open OrderedRuntime.Structured (Data Threaded)
open Sequential.Flat.Serial (WirePorts payloadData)
open NestedTheta.ExplicitRuntime.PurePrefix (EntryChecked)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {args : Ports (OrderedRuntime.Structured.Ty τ)} {a : Data args}
variable {A X Z L E D : τ} {ps qs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {headGraph : NestedTheta.Graph (PureGamma.Op (τ := τ) Φ ε) (Threaded args) [] ps (WirePorts A X Z)}

/-- Link a mixed producer to a continuation compiled through the existing
public translation. The producer returns the continuation's full carrier. -/
def compile (producer : EntryChecked (a := a) (b := payloadData A X Z) headGraph.toTerm)
    (suffix : Source Φ A X Z L E D qs) :=
  NestedTheta.ExplicitRuntime.PurePrefix.Splice.graph producer suffix.compileChecked

def compileChecked (producer : EntryChecked (a := a) (b := payloadData A X Z) headGraph.toTerm)
    (suffix : Source Φ A X Z L E D qs) :
    EntryChecked (a := a) (b := payloadData L E D) (compile producer suffix).toTerm :=
  NestedTheta.ExplicitRuntime.PurePrefix.Splice.graphChecked producer suffix.compileChecked

/-- A suffix recovered in the existing recursive layout can be used
directly, retaining its checked numbered table. -/
def linkRecovered (producer : EntryChecked (a := a) (b := payloadData A X Z) headGraph.toTerm)
    {g : Sequential.Flat.Serial.Graph Φ A X Z L E D qs} (suffix : Fibre .mixed g) :=
  NestedTheta.ExplicitRuntime.PurePrefix.Splice.graph producer (StructuredCFG.WithNestedFeedback.Related.checked suffix.2)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation
