module

public import Silmaril.SSA.RVSDG.LambdaSSA.PureRow.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Isomorphism.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.PureRow.Agreement

/-! # Relocating a total, independent pure row preserves numbered execution -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.PureRow

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (point)
open NestedTheta.Partial (observe)
open NestedTheta.Partial.Executable (Actions run kindEval run_iff_observe)

universe u
variable {τ Φ ε σ : Type u} [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A P B C : τ}

/-- The pure row and first ordered row have independent inputs.
Swapping them leaves the producer of the second row's token intact. -/
theorem Segment.relocate (s : Segment Φ ε A P B C) :
    NestedTheta.Graph.Isomorphic (Op Φ ε) s.early.toGraph s.late.toGraph :=
  Proofs.relocate s

/-- Moving the first ordered row to the second's position would change
an argument token into a predecessor result, which no vertex map can do. -/
theorem Segment.effect_order (s : Segment Φ ε A P B C) (ids : Fin 3 ≃ Fin 3) (movesFirst : ids 1 = 2) :
    ¬ ∀ i, (s.early.toGraph.nodes i).inputs.addresses.map (Address.rename (renameVertex ids)) =
      (s.early.toGraph.nodes (ids i)).inputs.addresses :=
  Proofs.effect_order s ids movesFirst

variable [TypeFormers τ] [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]

theorem typingAt_denotes (p : TwoBlock.Instruction Φ A C) {Γ : List τ} {i : Nat} (hi : Γ[i]? = some A) :
    Denotes (m := StateT σ Part.{u}) ε (typingAt p hi) (fun env => TwoBlock.call (ε := ε) p (Env.get env i hi)) :=
  Proofs.callAt p hi

theorem call_bottom (p : TwoBlock.Instruction Φ A P) (h : (instrEff p.op : ε) = ⊥) (x : TyDen A) :
    TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) p x = pure (pureCall (σ := σ) p h x) :=
  Proofs.call_bottom p h x

variable (s : Segment Φ ε A P B C)
variable (actions : Actions (model (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)))

theorem Segment.region_denote
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) (env : Env [A]) :
    Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env =
      (TwoBlock.call (ε := ε) s.first env.2 >>= fun _ =>
        TwoBlock.call (ε := ε) s.second env.2 >>= fun result =>
          pure (.inl ((TypeModel.productEquiv P C).symm (pureCall (σ := σ) s.value s.bottom env.2, result)))) :=
  Proofs.flat_run s coherent env

omit [HasTy Φ τ] [HasEff Φ ε] [Bot ε] [InstructionModel Φ τ ε (StateT σ Part.{u})] in
theorem mapped_exit_iff (result : Part (LabelDen [Silmaril.product P C] × σ))
    (exit : LabelDen [Silmaril.product P C]) (final : σ) :
    Part.map encodeExit result = Part.some (encodeExit (exit, final)) ↔ result = Part.some (exit, final) :=
  Proofs.mapped_exit_iff result exit final

theorem Segment.run_eq (fuel : Nat) (x : TyDen A) (initial : σ) :
    run actions s.early.toGraph fuel (point x initial) = run actions s.late.toGraph fuel (point x initial) :=
  s.relocate.evalWith_eq (kindEval actions fuel) (point x initial)

variable {rows : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {actual : NestedTheta.Graph (Op Φ ε) (Wire A) [] rows (Output P C)}

/-- Compare a checked relocation of the numbered segment to the actual
flat LambdaSSA block with the pure binding in source order. -/
theorem Segment.region_observe
    (numbering : NestedTheta.Graph.Isomorphic (Op Φ ε) s.early.toGraph actual)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (model (Φ := Φ) (ε := ε) (σ := σ)) actual (point env.2 initial) =
      Part.map (encodeExit (P := P) (C := C))
        ((Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env).run initial) :=
  (NestedTheta.Partial.observe_iso numbering (model (Φ := Φ) (ε := ε) (σ := σ)) _).symm.trans
    (Proofs.agrees s coherent env initial)

theorem Segment.finite_returns_iff
    (numbering : NestedTheta.Graph.Isomorphic (Op Φ ε) s.early.toGraph actual)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [Silmaril.product P C]) (initial final : σ) :
    (∃ fuel, run actions actual fuel (point env.2 initial) = some (encodeExit (exit, final))) ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) s.typing env).run initial = Part.some (exit, final) := by
  refine (run_iff_observe actions actual (point env.2 initial) (encodeExit (exit, final))).trans ?_
  rw [s.region_observe numbering coherent env initial]
  exact mapped_exit_iff _ exit final

end Silmaril.SSA.RVSDG.LambdaSSA.PureRow
