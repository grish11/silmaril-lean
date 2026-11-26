module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Reverse.Agreement

/-! # Actual flat denotation of the recovered mixed pipeline -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Reverse

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open PureGamma (Choice model entry)
open NestedTheta.Partial (observe)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A M E D : τ} {g : Graph Φ ε A M E D}

/-- The full partial observation of the input numbered graph agrees with the
recovered flat region, including the result label and exact current token. -/
theorem Fibre.region_observe (f : Fibre g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [Choice A]) (initial : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) g (entry env.2 initial) =
      Part.map (ExplicitRuntime.exitTuple (A := M))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) f.fragment.typing env).run initial) := by
  rcases f with ⟨s, rfl⟩
  exact Proofs.emit_observe s coherent env initial

/-- A numbered run returns at some finite fuel exactly when the flat region
returns the same typed exit, payload, and final token. -/
theorem Fibre.run_iff (f : Fibre g) (base : Actions (τ := τ) (ε := ε) (σ := σ) Φ)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [Choice A]) (label : LabelDen [E,D]) (initial final : σ) :
    (∃ fuel, NestedTheta.Partial.Executable.run (PureGamma.actions base) g fuel (entry env.2 initial) =
      some (ExplicitRuntime.exitTuple (A := M) (label, final))) ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) f.fragment.typing env).run initial =
        Part.some (label, final) := by
  refine (NestedTheta.Partial.Executable.run_iff_observe (PureGamma.actions base) g _ _).trans ?_
  rw [f.region_observe coherent env initial]
  exact Translation.mapped_exit_iff _ _ _

/-- Absence of a finite return agrees at the partial boundary. -/
theorem Fibre.no_return_iff (f : Fibre g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [Choice A]) (initial : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) g (entry env.2 initial) = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) f.fragment.typing env).run initial = Part.none := by
  rw [f.region_observe coherent env initial]
  refine Part.eq_none_iff'.trans ?_
  change ¬((Region.denote (ε := ε) (m := StateT σ Part.{u}) f.fragment.typing env).run initial).Dom ↔ _
  exact Part.eq_none_iff'.symm

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedContinuation.Reverse
