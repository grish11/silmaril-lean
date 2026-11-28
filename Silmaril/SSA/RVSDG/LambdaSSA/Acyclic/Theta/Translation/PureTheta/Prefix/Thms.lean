module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Flat.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Executable.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Agreement

/-! # Exact finite observations of the recovered mixed prefix -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (point carriedData)
open OrderedRuntime.Structured (RuntimeValues)
open TwoBlock.TwoExit (enter)
open PureGamma (model)
open NestedTheta.Partial (observe)
open Sequential

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A X Z L E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {g : Graph Φ ε A X Z L E D sigs}

/-- Carrier conversion uses the raw graph's returned payload and token. -/
theorem enterGraph_observe {raw : NestedTheta.Graph (PureGamma.Op (τ := τ) Φ ε)
      (InputPorts A) [] sigs (InputPorts A)}
    (head : NestedTheta.ExplicitRuntime.PurePrefix.EntryChecked
      (a := carriedData A) (b := carriedData A) raw.toTerm)
    (input : Tuple (RuntimeValues (TyDen (τ := τ)) σ) (InputPorts A)) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) (enterGraph head X Z) input =
      Part.map (fun p => point (enter (A := A) (C := X) (D := Z) (p.get .head)) (p.get (.tail .head)))
        (observe (model (Φ := Φ) (ε := ε) (σ := σ)) raw input) :=
  Proofs.enterGraph_observe head input

/-- The recursive suffix executes on the exact payload and live token
returned by the mixed θ. -/
theorem compile_observe (s : Loop Φ ε A) (pureFirst : Bool)
    (tail : StructuredCFG.WithNestedFeedback.Syntax Φ A X Z L E D sigs) (x : TyDen A) (initial : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) (compile s pureFirst tail) (point x initial) =
      (observe (model (Φ := Φ) (ε := ε) (σ := σ)) (s.compile pureFirst) (point x initial)).bind
        (fun p => Flat.Serial.observe (ε := ε) (σ := σ) (Translation.compile (.mixed tail))
          (p.get .head) (p.get (.tail .head))) :=
  Proofs.compile_observe s pureFirst tail x initial

theorem Fibre.region_observe (f : Fibre g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) g (point env.2 initial) =
      Part.map (ExplicitRuntime.exitTuple (A := L))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) f.fragment.typing env).run initial) := by
  rcases f with ⟨c, rfl⟩
  exact Proofs.candidate_observe c coherent env initial

/-- Any finite return of the input table preserves and reflects the actual
flat region's exit label, typed payload and final token. -/
theorem Fibre.run_iff (f : Fibre g) (base : Actions (τ := τ) (ε := ε) (σ := σ) Φ)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (label : LabelDen [E,D]) (initial final : σ) :
    (∃ fuel, NestedTheta.Partial.Executable.run (PureGamma.actions base) g fuel (point env.2 initial) =
        some (ExplicitRuntime.exitTuple (A := L) (label, final))) ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) f.fragment.typing env).run initial =
        Part.some (label, final) := by
  refine (NestedTheta.Partial.Executable.run_iff_observe (PureGamma.actions base) g _ _).trans ?_
  rw [f.region_observe coherent env initial]
  exact Translation.mapped_exit_iff _ _ _

/-- Absence of a finite return agrees at the partial-result boundary. -/
theorem Fibre.no_return_iff (f : Fibre g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) g (point env.2 initial) = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) f.fragment.typing env).run initial = Part.none := by
  rw [f.region_observe coherent env initial]
  refine Part.eq_none_iff'.trans ?_
  change ¬((Region.denote (ε := ε) (m := StateT σ Part.{u}) f.fragment.typing env).run initial).Dom ↔ _
  exact Part.eq_none_iff'.symm

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix
