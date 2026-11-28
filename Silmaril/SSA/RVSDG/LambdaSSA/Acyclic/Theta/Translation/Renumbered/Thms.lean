module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Renumbered.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Executable.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Isomorphism.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Isomorphism.Thms

/-! # Agreement at the actual numbered graph and recovered SSA boundary -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation

open Sequential
open Flat.Serial (observe)
open Flat.Numbered.Recognize (opcodeCode)
open NestedTheta.Isomorphism (Mapping check)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (point)
open TwoBlock.TwoExit (enter)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z L E D : τ}
variable {ps qs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {actual : Flat.Serial.Graph Φ A X Z L E D ps} {canonical : Flat.Serial.Graph Φ A X Z L E D qs}
variable {layout : Layout τ A X Z L E D qs}

/-- Every emitted scope and child scope has a predecessor dependency.
The rank-rigidity theorem then fixes the local vertex order of each scope
under any typed isomorphism to this emission. -/
theorem Source.compile_scopeChains (s : Source Φ A X Z L E D qs) : (compile s).ScopeChains := by
  simpa only [NestedTheta.Graph.toGraph_toTerm] using s.compileChecked.scopeChains

namespace Renumbered

/-- For a compiled representative the row-map check suffices for recovery. -/
theorem recover_compiled_iff [DecidableEq τ] [DecidableEq Φ]
    (s : Source Φ A X Z L E D qs) (mapping : Mapping) :
    (recover actual (compile s) s.layout mapping).isSome =
      (check (opcodeCode (τ := τ) (Φ := Φ)) mapping actual (compile s)).isSome := by
  cases same : check (opcodeCode (τ := τ) (Φ := Φ)) mapping actual (compile s) <;>
    simp [recover, same, Translation.recover_compiled]

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

theorem Fibre.region_observe (f : Fibre actual canonical layout)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) actual env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := L))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) f.recovered.typing env).run initial) :=
  (NestedTheta.Partial.observe_iso f.numbering (Wires.wireModel (ε := ε)) _).trans
    (f.recovered.region_observe coherent env initial)

theorem Fibre.run_eq (f : Fibre actual canonical layout)
    (actions : Actions (τ := τ) (ε := ε) (σ := σ) Φ) (fuel : Nat) (input : TyDen A) (initial : σ) :
    run actions actual fuel input initial = run actions canonical fuel input initial :=
  f.numbering.evalWith_eq (NestedTheta.Partial.Executable.kindEval actions fuel) (point (enter input) initial)

theorem Fibre.run_iff (f : Fibre actual canonical layout)
    (actions : Actions (τ := τ) (ε := ε) (σ := σ) Φ)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    (∃ fuel, run actions actual fuel env.2 initial = some (ExplicitRuntime.exitTuple (A := L) (exit, final))) ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) f.recovered.typing env).run initial =
        Part.some (exit, final) := by
  simp only [f.run_eq actions]
  exact f.recovered.run_iff actions coherent env exit initial final

end Renumbered
end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation
