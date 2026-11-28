module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Flat.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Reverse.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Flat.Agreement

/-! # Exact observations across the flat continuation -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Sequential
open OrderedTheta (point)
open Silmaril.Elgot (iter)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A X Z L E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- Both mixed body orders recover with any compiled public continuation. -/
theorem recoverLink_compiled [DecidableEq τ] [DecidableEq Φ] (s : Loop Φ ε A)
    (pureFirst : Bool) (tail : Source Φ A X Z L E D sigs) :
    (recoverLink (s.compile pureFirst) tail.layout (Translation.compile tail)).isSome = true := by
  obtain ⟨f, found⟩ := Option.isSome_iff_exists.mp (Translation.recover_compiled tail)
  simp [recoverLink, Reverse.recover_generated, found]

variable {σ : Type u} [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

theorem Loop.fragment_denote (s : Loop Φ ε A)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) (env : Env [A]) :
    Region.denote (ε := ε) (m := StateT σ Part.{u}) s.fragment.typing env =
      iter s.step env.2 >>= fun y => pure (.inl y) :=
  Proofs.loop_fragment_denote s coherent env

/-- Observe the two component tables in order and compare with the one
relocated flat CFG. The suffix receives the returned payload and exact
token. The equality also covers absence of a finite return. -/
theorem Link.region_observe {g : Reverse.Graph Φ ε A} {layout : Layout τ A X Z L E D sigs}
    {h : Flat.Serial.Graph Φ A X Z L E D sigs} (f : Link g layout h)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    (NestedTheta.Partial.observe (PureGamma.model (Φ := Φ) (ε := ε) (σ := σ))
      g (point env.2 initial)).bind (fun output =>
        Flat.Serial.observe (ε := ε) (σ := σ) h (output.get .head) (output.get (.tail .head))) =
      Part.map (ExplicitRuntime.exitTuple (A := L))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) f.fragment.typing env).run initial) :=
  Proofs.link_observe f coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta
