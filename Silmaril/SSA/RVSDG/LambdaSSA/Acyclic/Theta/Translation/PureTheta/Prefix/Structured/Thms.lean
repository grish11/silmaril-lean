module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Structured.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Structured.Agreement

/-! # Agreement of a mixed choice tree and the public ordered continuation -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Structured

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (point)
open NestedTheta.Partial (observe)
open PureGamma (model)
open Sequential

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A X Z L E D : τ} {ps qs rows : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {g : Graph Φ ε A L E D rows}

/-- A selected arm returns a raw payload and the updated token, at every
depth of the choice tree. -/
theorem Tree.region_observe (tree : Tree Φ ε A rows)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) tree.graph (point env.2 initial) =
      Part.map (fun p => point (merge p.1) p.2)
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) tree.fragment.typing env).run initial) :=
  Proofs.tree_observe tree coherent env initial

theorem compile_region_observe (head : Tree Φ ε A ps)
    (tail : StructuredCFG.WithNestedFeedback.Syntax Φ A X Z L E D qs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) (compile head tail) (point env.2 initial) =
      Part.map (ExplicitRuntime.exitTuple (A := L))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) (Flat.link head.fragment tail.source).typing env).run initial) :=
  Proofs.compile_agrees head tail coherent env initial

theorem Fibre.region_observe (f : Fibre g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) g (point env.2 initial) =
      Part.map (ExplicitRuntime.exitTuple (A := L))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) f.fragment.typing env).run initial) := by
  rcases f with ⟨c, rfl⟩
  exact Proofs.emit_observe c coherent env initial

/-- Any successful recovery of a compiled tree agrees with the original
flat CFG at every input, including absence of finite return. -/
theorem Fibre.compiled_denote (head : Tree Φ ε A ps)
    (tail : StructuredCFG.WithNestedFeedback.Syntax Φ A X Z L E D qs) (f : Fibre (compile head tail))
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u}) f.fragment.typing env).run initial =
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) (Flat.link head.fragment tail.source).typing env).run initial :=
  Proofs.compiled_denote head tail f coherent env initial

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

theorem Fibre.no_return_iff (f : Fibre g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) g (point env.2 initial) = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) f.fragment.typing env).run initial = Part.none := by
  rw [f.region_observe coherent env initial]
  refine Part.eq_none_iff'.trans ?_
  change ¬((Region.denote (ε := ε) (m := StateT σ Part.{u}) f.fragment.typing env).run initial).Dom ↔ _
  exact Part.eq_none_iff'.symm

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Structured
