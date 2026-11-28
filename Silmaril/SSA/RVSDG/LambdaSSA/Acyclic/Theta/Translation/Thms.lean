module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Normalization.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Reverse.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Thms

/-! # A shared observation of the input graph and recovered LambdaSSA -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Sequential
open Sequential.Flat.Serial
open StructuredCFG

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {layout : Layout τ A X Z L E D sigs} {g : Flat.Serial.Graph Φ A X Z L E D sigs}

/-- Each forward compiler emits graphs accepted by its selected layout. -/
theorem recover_compiled [DecidableEq τ] [DecidableEq Φ] (source : Source Φ A X Z L E D sigs) :
    (recover source.layout (compile source)).isSome = true :=
  match source with
  | .mixed s => WithNestedFeedback.Normalization.compile_recover s
  | .routed s => Routed.Reverse.complete_generated s (NestedTheta.Graph.Isomorphic.refl _)
  | .routedMixed s h => by simp only [Source.layout, compile, recover, Routed.Mixed.recover_generated s h,
      Option.isSome_some]

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- Compare the full partial observation of the input graph to the actual
recovered region. The exit encoding retains its label, typed payload and
final token. An absent observation denotes no finite return. -/
theorem Fibre.region_observe (f : Fibre layout g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := L))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) f.typing env).run initial) := by
  cases layout with
  | mixed => exact WithNestedFeedback.Related.region_observe f.2 coherent env initial
  | routed => exact Routed.Reverse.Related.region_observe f.2 coherent env initial
  | routedMixed => exact Routed.Mixed.Related.region_observe f.2 coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation
