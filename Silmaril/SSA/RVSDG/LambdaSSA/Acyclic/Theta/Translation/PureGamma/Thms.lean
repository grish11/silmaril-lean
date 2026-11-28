module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.PureRow.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Agreement

/-! # Exact observations of the checked γ lowering -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open NestedTheta.Partial.Executable (run_iff_observe)
open PureRow (encodeExit)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A P B C : τ}
variable (s : Branch Φ ε A P B C)

theorem Branch.region_denote
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) (env : Env [Choice A]) :
    Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env =
      match TypeModel.coprodEquiv A A env.2 with
      | .inl x => Region.denote (ε := ε) (m := StateT σ Part.{u}) s.left.typing (PUnit.unit, x)
      | .inr x => Region.denote (ε := ε) (m := StateT σ Part.{u}) s.right.typing (PUnit.unit, x) :=
  Proofs.region_denote s coherent env

/-- Both placements preserve the full partial observation of the flat case,
including the selected arm's exact final token. -/
theorem Branch.region_observe (pureFirst : Bool)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [Choice A]) (initial : σ) :
    NestedTheta.Partial.observe (model (Φ := Φ) (ε := ε) (σ := σ)) (s.compile pureFirst) (entry env.2 initial) =
      Part.map (encodeExit (P := P) (C := C))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env).run initial) :=
  Proofs.agrees s pureFirst coherent env initial

theorem Branch.run_iff (base : Actions (τ := τ) (ε := ε) (σ := σ) Φ) (pureFirst : Bool)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [Choice A]) (exit : LabelDen [Silmaril.product P C]) (initial final : σ) :
    (∃ fuel, NestedTheta.Partial.Executable.run (actions base) (s.compile pureFirst) fuel (entry env.2 initial) =
      some (encodeExit (exit, final))) ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env).run initial = Part.some (exit, final) := by
  refine (run_iff_observe (actions base) (s.compile pureFirst) _ _).trans ?_
  rw [s.region_observe pureFirst coherent env initial]
  exact PureRow.mapped_exit_iff _ exit final

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma
