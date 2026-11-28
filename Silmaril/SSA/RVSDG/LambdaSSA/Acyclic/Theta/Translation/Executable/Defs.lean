module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable.Defs

/-! # Operational execution of the translated ordered-state layouts -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation

open Isotope.LetIter.ProofRelevant.Semantics
open Sequential
open StructuredCFG
open OrderedTheta (point)
open TwoBlock.TwoExit (enter)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- The original typed flat CFG of an admitted source. -/
def Source.fragment (source : Source Φ A X Z L E D sigs) : Flat.Fragment Φ A E D :=
  match source with
  | .mixed s => s.source
  | .routed s => s.source
  | .routedMixed s _ => s.source

/-- Numbering retains the single-live-token admission in each layout. -/
def Source.compileChecked (source : Source Φ A X Z L E D sigs) :
    NestedTheta.ExplicitRuntime.EntryChecked
      (a := Flat.Serial.payloadData A X Z) (b := Flat.Serial.payloadData L E D) (compile source).toTerm :=
  match source with
  | .mixed s => WithNestedFeedback.Normalization.compileChecked s
  | .routed s => (Flat.Serial.Routed.Related.generated s).checked
  | .routedMixed s _ => s.checked

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

abbrev Actions (Φ : Type u) [HasTy Φ τ] [HasEff Φ ε] [InstructionModel Φ τ ε (StateT σ Part.{u})] :=
  NestedTheta.Partial.Executable.Actions (Wires.wireModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ))

/-- Run the numbered graph from its SSA entry value and explicit token. -/
def run (actions : Actions (τ := τ) (ε := ε) (σ := σ) Φ)
    (g : Flat.Serial.Graph Φ A X Z L E D sigs) (fuel : Nat) (input : TyDen A) (initial : σ) :
    Option (Tuple (OrderedRuntime.Structured.RuntimeValues (TyDen (τ := τ)) σ) (Flat.Serial.WirePorts L E D)) :=
  NestedTheta.Partial.Executable.run actions g fuel (point (enter input) initial)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation
