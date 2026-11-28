module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Agreement

/-! # Finite observations of the mixed numbered θ loop -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot (iter)
open OrderedTheta (exit point)
open PureGamma (model)
open NestedTheta.Partial.Executable (run_iff_observe)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A : τ}
variable (s : Loop Φ ε A)

/-- The actual numbered table agrees with iteration of the typed activation
at its carried value and live-token boundary. -/
theorem Loop.step_observe (pureFirst : Bool) (input : TyDen A) (initial : σ) :
    NestedTheta.Partial.observe (model (Φ := Φ) (ε := ε) (σ := σ)) (s.compile pureFirst) (point input initial) =
      Part.map (fun (output, final) => point output final) ((iter (s.step (σ := σ)) input).run initial) :=
  Proofs.graph_observe s pureFirst input initial

theorem Loop.region_denote
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) (env : Env [A]) :
    Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env =
      iter (s.step (σ := σ)) env.2 >>= fun a => pure (exit a) :=
  Proofs.region_denote s coherent env

/-- The pure row can be emitted on either side of the ordered instruction.
The numbered loop and the actual flat CFG retain the same partial result. -/
theorem Loop.region_observe (pureFirst : Bool)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    NestedTheta.Partial.observe (model (Φ := Φ) (ε := ε) (σ := σ)) (s.compile pureFirst) (point env.2 initial) =
      Part.map encodeExit ((Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env).run initial) :=
  Proofs.agrees s pureFirst coherent env initial

theorem Loop.run_iff (base : Actions (τ := τ) (ε := ε) (σ := σ) Φ) (pureFirst : Bool)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (output : TyDen A) (initial final : σ) :
    (∃ fuel, s.run base pureFirst fuel env.2 initial = some (point output final)) ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env).run initial =
        Part.some (exit output, final) := by
  refine (run_iff_observe (PureGamma.actions base) (s.compile pureFirst) _ _).trans ?_
  rw [s.region_observe pureFirst coherent env initial]
  exact Proofs.mapped_exit_iff _ output final

/-- Compare the absence of a finite observation. Its cause is outside the
partial result at this boundary. -/
theorem Loop.no_return_iff (pureFirst : Bool)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    NestedTheta.Partial.observe (model (Φ := Φ) (ε := ε) (σ := σ))
        (s.compile pureFirst) (point env.2 initial) = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env).run initial = Part.none := by
  rw [s.region_observe pureFirst coherent env initial]
  let result := (Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env).run initial
  change Part.map encodeExit result = Part.none ↔ result = Part.none
  refine Part.eq_none_iff'.trans ?_
  change ¬result.Dom ↔ result = Part.none
  exact Part.eq_none_iff'.symm

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta
