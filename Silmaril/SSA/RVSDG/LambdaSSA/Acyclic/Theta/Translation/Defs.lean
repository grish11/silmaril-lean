module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Normalization.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Defs

/-! # Public translation for the mixed and routed ordered-state layouts

Use `compile` on an admitted source and `recover` on a numbered graph with
the expected layout. The recovered fibre contains a typed flat region and
evidence tied to the supplied graph and layout.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation

open Isotope.LambdaSSA (Region)
open Sequential
open Sequential.Flat.Serial
open StructuredCFG

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- The selected decoder determines the supported layout at the typed
graph boundary. Mixed links use homogeneous joins and may include nested
feedback. Routed links end in a γ with a bypass arm and a consumer arm. The
mixed routed layout recursively composes such links with canonical mixed leaves. -/
inductive Layout (τ : Type u) [TypeFormers τ] :
    τ → τ → τ → τ → τ → τ → List (Ports (OrderedRuntime.Structured.Ty τ)) → Type u where
  | mixed {A X Z L E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} :
      Layout τ A X Z L E D sigs
  | routed {A E M D : τ} : Layout τ A E M M E D (Routed.Signatures A E M D)
  | routedMixed {A X Z L E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} :
      Layout τ A X Z L E D sigs

/-- The admitted source syntax determines the layout and the typed boundaries. -/
inductive Source (Φ : Type u) [HasTy Φ τ] :
    τ → τ → τ → τ → τ → τ → List (Ports (OrderedRuntime.Structured.Ty τ)) → Type u where
  | mixed {A X Z L E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} :
      WithNestedFeedback.Syntax Φ A X Z L E D sigs → Source Φ A X Z L E D sigs
  | routed {A B K E M C J D : τ} :
      Routed.Source Φ A B K M C J E D → Source Φ A E M M E D (Routed.Signatures A E M D)
  | routedMixed {A X Z L E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
      (s : Routed.Mixed.Component Φ A X Z L E D sigs) :
      s.Supported → Source Φ A X Z L E D sigs

def Source.layout (source : Source Φ A X Z L E D sigs) : Layout τ A X Z L E D sigs :=
  match source with
  | .mixed _ => .mixed
  | .routed _ => .routed
  | .routedMixed _ _ => .routedMixed

/-- Emit the layout accepted by the corresponding canonical decoder. -/
def compile (source : Source Φ A X Z L E D sigs) : Flat.Serial.Graph Φ A X Z L E D sigs :=
  match source with
  | .mixed s => WithNestedFeedback.Normalization.compile s
  | .routed s => s.graph
  | .routedMixed s _ => s.graph

abbrev Related (layout : Layout τ A X Z L E D sigs) (g : Flat.Serial.Graph Φ A X Z L E D sigs) (r : Region Φ) : Type u :=
  match layout with
  | .mixed => WithNestedFeedback.Related A X Z L E D sigs r g
  | .routed => Routed.Reverse.Related g r
  | .routedMixed => Routed.Mixed.Related g r

/-- A recovered flat LambdaSSA region and the selected decoder's
certificate for this particular input graph. -/
abbrev Fibre (layout : Layout τ A X Z L E D sigs) (g : Flat.Serial.Graph Φ A X Z L E D sigs) :=
  Σ r : Region Φ, Related layout g r

/-- Keep the typed block table represented by the recovered region.
It can be relocated by the existing flat link and fork operations. -/
def Fibre.fragment {layout : Layout τ A X Z L E D sigs} {g : Flat.Serial.Graph Φ A X Z L E D sigs}
    (f : Fibre layout g) : Flat.Fragment Φ A E D := by
  rcases f with ⟨r, witness⟩
  cases layout with
  | mixed => cases witness with | generated source => exact source.source
  | routed => cases witness with | routed source _ => exact source.source
  | routedMixed => cases witness with | generated source _ => exact source.source

theorem Fibre.fragment_region {layout : Layout τ A X Z L E D sigs}
    {g : Flat.Serial.Graph Φ A X Z L E D sigs} (f : Fibre layout g) : f.fragment.region = f.1 := by
  rcases f with ⟨r, witness⟩
  cases layout <;> cases witness <;> rfl

theorem Fibre.typing {layout : Layout τ A X Z L E D sigs} {g : Flat.Serial.Graph Φ A X Z L E D sigs}
    (f : Fibre layout g) : Region.HasType [A] f.1 [E,D] := by
  cases layout with
  | mixed => exact WithNestedFeedback.Related.typing f.2
  | routed => exact Routed.Reverse.Related.typing f.2
  | routedMixed => exact Routed.Mixed.Related.typing f.2

/-- Recover in the requested canonical layout. `none` means that its
parser or exact wiring certification rejected the input. The specialized
checked-isomorphism entry points remain available for separate graph views. -/
def recover [DecidableEq τ] [DecidableEq Φ] (layout : Layout τ A X Z L E D sigs)
    (g : Flat.Serial.Graph Φ A X Z L E D sigs) : Option (Fibre layout g) := by
  cases layout with
  | mixed => exact WithNestedFeedback.Reverse.Recursive.recover g
  | routed => exact Routed.Reverse.recognize g
  | routedMixed => exact Routed.Mixed.recover g

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation
