module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Complete

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A E M D : τ}

/-- The existing component parsers recover both local views on the
supported canonical emission. The exact check certifies the joined graph. -/
theorem recover_generated [DecidableEq τ] [DecidableEq Φ] (s : Components Φ A E M D) (h : s.Supported) :
    recover s.graph = some ⟨s.source.region, .generated s rfl⟩ := by
  rw [recover, Proofs.candidate_generated s h, Option.bind_some]
  simp [certify]

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

theorem Components.agrees (s : Components Φ A E M D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) s.source s.graph :=
  splice_agrees (Spine.loop s.producer).code s.consumer.toSyntax.code
    ((Spine.loop s.producer).agrees coherent) (s.consumer.toSyntax.agrees coherent) coherent

theorem Related.region_observe {g : Reverse.CanonicalGraph Φ A E M D}
    {r : Isotope.LambdaSSA.Region Φ} (w : Related g r)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := M))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial) := by
  cases w with
  | generated s wiring => exact wiring ▸ s.agrees coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed
