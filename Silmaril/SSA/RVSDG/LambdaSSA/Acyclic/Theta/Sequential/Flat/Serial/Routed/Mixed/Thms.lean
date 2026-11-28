module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Complete
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Agreement

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- The recursive parser recovers the canonical emission of supported leaves
and cuts. The exact check certifies the entire graph. -/
theorem recover_generated [DecidableEq τ] [DecidableEq Φ] (s : Component Φ A X Z L E D sigs) (h : s.Supported) :
    recover s.graph = some ⟨s.source.region, .generated s rfl⟩ := by
  rw [recover, Proofs.candidate_generated s h, Option.bind_some]
  simp [certify]

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- Compose the semantic splice independently of canonical recovery.
The premises on each leaf are the coherent ordered-state interpretation. -/
theorem Component.agrees (s : Component Φ A X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    Agrees (ε := ε) (σ := σ) s.source s.graph :=
  Proofs.agrees s coherent

theorem Related.region_observe {g : Graph Φ A X Z L E D sigs}
    {r : Isotope.LambdaSSA.Region Φ} (w : Related g r)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := L))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial) := by
  cases w with
  | generated s wiring => exact wiring ▸ s.agrees coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed
