module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Renumbered.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Normalization.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Isomorphism.Thms

/-! # Partial state agreement at the actual numbered graph boundary -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Renumbered

open Sequential
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {g : Flat.Serial.Graph Φ A X Z L E D sigs} {r : Isotope.LambdaSSA.Region Φ}

/-- The representative is accepted exactly when it has the canonical mixed
layout. The supplied isomorphism fixes all operand, result and child ports. -/
theorem recover_isSome_iff [DecidableEq τ] [DecidableEq Φ] (view : View g) :
    (recover g view).isSome = true ↔
      ∃ n : Recursive.Normal Φ A X Z L E D view.signatures, n.toSyntax.graph = view.representative := by
  simpa [recover] using Recursive.recover_isSome_iff view.representative

/-- A checked view of a compiled source is accepted without a separate parse witness. -/
theorem recover_compiled [DecidableEq τ] [DecidableEq Φ]
    {canonicalSigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
    (s : Syntax Φ A X Z L E D canonicalSigs)
    (numbering : NestedTheta.Graph.Isomorphic (Wires.Op Φ) g (Normalization.compile s)) :
    (recover g ⟨canonicalSigs, Normalization.compile s, numbering⟩).isSome = true := by
  simpa [recover] using Normalization.compile_recover s

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- Compare the actual graph to the recovered flat source, using the same
explicit value and state token model at either graph boundary. -/
theorem Related.region_observe (w : Related g r)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    Flat.Serial.observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := L))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial) :=
  (NestedTheta.Partial.observe_iso w.view.numbering (Wires.wireModel (ε := ε)) _).trans
    (w.canonical.region_observe coherent env initial)

theorem Related.region_returns_iff (w : Related g r)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    Flat.Serial.returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.some (exit, final) :=
  (NestedTheta.Partial.returns_iso_iff w.view.numbering (Wires.wireModel (ε := ε)) _ _).trans
    (w.canonical.region_returns_iff coherent env exit initial final)

theorem Related.region_undefined_iff (w : Related g r)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    Flat.Serial.observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.none := by
  rw [show Flat.Serial.observe (ε := ε) g env.2 initial =
    Flat.Serial.observe (ε := ε) w.view.representative env.2 initial
    from NestedTheta.Partial.observe_iso w.view.numbering (Wires.wireModel (ε := ε)) _]
  exact w.canonical.region_undefined_iff coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Renumbered
