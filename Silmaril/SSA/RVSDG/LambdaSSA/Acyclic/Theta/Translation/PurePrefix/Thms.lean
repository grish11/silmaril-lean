module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PurePrefix.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Executable.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PurePrefix.Agreement

/-! # Exact finite returns of a checked pure entry prefix -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PurePrefix

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (point carriedData)
open Sequential
open NestedTheta.Partial.Executable (run_iff_observe)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A R B X Z L E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

theorem orderedCall_denote (p : TwoBlock.Instruction Φ A R) (x : TyDen A) (initial : σ) :
    (Wires.wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive
      (.ordered (carriedData A) (carriedData R) (orderedCall p)) (point x initial) =
      Part.map (fun (y, token) => point y token)
        ((TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) p x).run initial) :=
  Proofs.orderedCall_denote p x initial

variable (setup : Prefix Φ ε A R B) (body : Source Φ B X Z L E D sigs)

theorem region_denote
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) (env : Env [A]) :
    Region.denote (ε := ε) (m := StateT σ Part.{u}) (typing setup body) env =
      TwoBlock.call (ε := ε) setup.action env.2 >>= fun _ =>
        Region.denote (ε := ε) (m := StateT σ Part.{u}) body.fragment.typing
          (PUnit.unit, PureRow.pureCall (σ := σ) setup.value setup.bottom env.2) :=
  Proofs.region_denote setup body coherent env

/-- The graph runs the ordered action and passes its exact token with the
new pure value to the unchanged structured continuation. -/
theorem region_observe (pureFirst : Bool)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    NestedTheta.Partial.observe (model (Φ := Φ) (ε := ε) (σ := σ))
        (compile setup body pureFirst) (point env.2 initial) =
      Part.map (ExplicitRuntime.exitTuple (A := L))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (typing setup body) env).run initial) :=
  Proofs.agrees setup body pureFirst coherent env initial

theorem run_iff (base : Translation.Actions (τ := τ) (ε := ε) (σ := σ) Φ) (pureFirst : Bool)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    (∃ fuel, NestedTheta.Partial.Executable.run (actions base) (compile setup body pureFirst) fuel
      (point env.2 initial) = some (ExplicitRuntime.exitTuple (A := L) (exit, final))) ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) (typing setup body) env).run initial =
        Part.some (exit, final) := by
  refine (run_iff_observe (actions base) (compile setup body pureFirst) _ _).trans ?_
  rw [region_observe setup body pureFirst coherent env initial]
  exact Translation.mapped_exit_iff _ exit final

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PurePrefix
