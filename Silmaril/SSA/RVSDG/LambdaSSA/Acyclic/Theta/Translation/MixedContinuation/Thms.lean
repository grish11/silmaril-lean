module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Executable.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Splice.Thms

/-! # Denotation at a mixed-to-ordered translation boundary -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedRuntime.Structured (Data Threaded)
open OrderedTheta (point)
open PureGamma (model evalValue OrderedModel)
open Sequential.Flat.Serial (WirePorts payloadData)
open NestedTheta.ExplicitRuntime.PurePrefix (EntryChecked)
open NestedTheta.Partial (observe)
open TwoBlock.TwoExit (enter)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {args : Ports (OrderedRuntime.Structured.Ty τ)} {a : Data args}
variable {A X Z L E D : τ} {ps qs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {headGraph : NestedTheta.Graph (PureGamma.Op (τ := τ) Φ ε) (Threaded args) [] ps (WirePorts A X Z)}

theorem compile_observe (producer : EntryChecked (a := a) (b := payloadData A X Z) headGraph.toTerm)
    (suffix : Source Φ A X Z L E D qs)
    (input : Tuple (model (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)).Val (Threaded args)) :
    observe model (compile producer suffix) input =
      observe model headGraph input >>= observe (OrderedModel (ε := ε)) (Translation.compile suffix) :=
  NestedTheta.ExplicitRuntime.PurePrefix.Splice.graph_observe (OrderedModel (ε := ε))
    evalValue producer suffix.compileChecked input

theorem linkRecovered_observe (producer : EntryChecked (a := a) (b := payloadData A X Z) headGraph.toTerm)
    {g : Sequential.Flat.Serial.Graph Φ A X Z L E D qs} (suffix : Fibre .mixed g)
    (input : Tuple (model (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)).Val (Threaded args)) :
    observe model (linkRecovered producer suffix) input =
      observe model headGraph input >>= observe (OrderedModel (ε := ε)) g :=
  NestedTheta.ExplicitRuntime.PurePrefix.Splice.graph_observe (OrderedModel (ε := ε)) evalValue producer
    (StructuredCFG.WithNestedFeedback.Related.checked suffix.2) input

/-- The recovered continuation's actual flat region runs at the payload
and token returned by the mixed producer. -/
theorem linkRecovered_observe_of_return (producer : EntryChecked (a := a) (b := payloadData A X Z) headGraph.toTerm)
    {g : Sequential.Flat.Serial.Graph Φ A X Z L E D qs} (suffix : Fibre .mixed g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (input : Tuple (model (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)).Val (Threaded args))
    (env : Env [A]) (mid : σ)
    (returned : observe model headGraph input = Part.some (point (enter env.2) mid)) :
    observe model (linkRecovered producer suffix) input =
      Part.map (ExplicitRuntime.exitTuple (A := L))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) suffix.typing env).run mid) := by
  rw [linkRecovered_observe, returned]
  exact (Part.bind_some _ _).trans (suffix.region_observe coherent env mid)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation
