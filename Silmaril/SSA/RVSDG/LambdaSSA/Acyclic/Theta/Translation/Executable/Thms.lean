module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Executable.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Executable.Blocks

/-! # Typed finite returns of the numbered operational runner -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Sequential
open StructuredCFG
open Flat.Serial (observe)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A X Z L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {layout : Layout τ A X Z L E D sigs}
variable {g : Flat.Serial.Graph Φ A X Z L E D sigs}
variable (actions : Actions (τ := τ) (ε := ε) (σ := σ) Φ)

private theorem mapped_exit_iff (result : Part (LabelDen [E,D] × σ)) (exit : LabelDen [E,D]) (final : σ) :
    Part.map (ExplicitRuntime.exitTuple (A := L)) result = Part.some (ExplicitRuntime.exitTuple (A := L) (exit, final)) ↔
      result = Part.some (exit, final) := by
  rw [Part.eq_some_iff, Part.mem_map_iff, Part.eq_some_iff]
  simp only [ExplicitRuntime.exitTuple_injective.eq_iff, exists_eq_right]

private theorem run_iff_of_observe {input : TyDen A} {initial : σ} {result : Part (LabelDen [E,D] × σ)}
    (h : observe (ε := ε) g input initial = Part.map (ExplicitRuntime.exitTuple (A := L)) result)
    (exit : LabelDen [E,D]) (final : σ) :
    (∃ fuel, run actions g fuel input initial = some (ExplicitRuntime.exitTuple (A := L) (exit, final))) ↔
      result = Part.some (exit, final) :=
  (NestedTheta.Partial.Executable.run_iff_observe actions g _ _).trans
    ((Iff.of_eq (congrArg (fun o => o = Part.some (ExplicitRuntime.exitTuple (A := L) (exit, final))) h)).trans
      (mapped_exit_iff result exit final))

/-- Successful executions return exactly the typed exit, payload and final
token of the recovered flat region in every supported layout. -/
theorem Fibre.run_iff (f : Fibre layout g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    (∃ fuel, run actions g fuel env.2 initial = some (ExplicitRuntime.exitTuple (A := L) (exit, final))) ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) f.typing env).run initial = Part.some (exit, final) :=
  run_iff_of_observe actions (f.region_observe coherent env initial) exit final

/-- The same finite-return law starts at the original flat source and
runs the compiled numbered graph. -/
theorem Source.compile_run_iff (source : Source Φ A X Z L E D sigs)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    (∃ fuel, run actions (compile source) fuel env.2 initial =
      some (ExplicitRuntime.exitTuple (A := L) (exit, final))) ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) source.fragment.typing env).run initial =
        Part.some (exit, final) := by
  cases source with
  | mixed s =>
    exact run_iff_of_observe actions
      (WithNestedFeedback.Normalization.compile_observe s coherent env initial) exit final
  | routed s => exact run_iff_of_observe actions (s.agrees coherent env initial) exit final
  | routedMixed s _ => exact run_iff_of_observe actions (s.agrees coherent env initial) exit final

/-- A finite block of the numbered graph rules out runner success at every
bound. A `none` result at a bound does not identify a block. -/
theorem run_eq_none_of_blocked
    (checked : NestedTheta.ExplicitRuntime.EntryChecked
      (a := Flat.Serial.payloadData A X Z) (b := Flat.Serial.payloadData L E D) g.toTerm)
    {input : TyDen A} {initial : σ}
    {attempt : NestedTheta.OrderedState.Partial.Block
      (NestedTheta.ExplicitRuntime.ThreadedOp (Wires.Effect Φ)) (TyDen (τ := τ)) σ}
    (blocked : NestedTheta.ExplicitRuntime.Partial.abnormal (Wires.model (ε := ε)) g
      (OrderedTheta.point (TwoBlock.TwoExit.enter input) initial) (.blocked attempt))
    (fuel : Nat) : run actions g fuel input initial = none :=
  Proofs.run_eq_none_of_blocked actions checked blocked fuel

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation
