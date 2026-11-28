module

public import Silmaril.SSA.Isotope.LambdaSSA.Flat.InstructionMap.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.Thms

import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Flat.PackingInstructionMap

/-! # Syntactic naturality of packing a relabelled finite CFG -/

public section

namespace Silmaril.Isotope.LambdaSSA.FiniteCFG

open Silmaril.Isotope.LambdaSSA

universe u v w

variable {Φ : Type u} {Ψ : Type v} (f : Φ → Ψ)

theorem routedFlat_mapInstr {labels n : Nat} (blocks : Nat) (r : Flat Φ labels n) :
    routedFlat blocks (r.mapInstr f) = (routedFlat blocks r).mapInstr f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Flat.routedFlat_mapInstr f blocks r

variable {τ : Type w} [TypeFormers τ] [HasTy Φ τ] [HasTy Ψ τ]
  (profiles : InstructionMap.PreservesTypes (τ := τ) f)
  {blocks exits : Nat} {R : Fin blocks → τ} {L : Fin exits → τ}
  {n : Nat} {β : BoundCtx τ n} {g : FiniteCFG Φ blocks exits n} (hg : g.HasType β R L)

theorem packedDispatcherRegion_mapInstr :
    packedDispatcherRegion (hg.mapInstr profiles) = (packedDispatcherRegion hg).mapInstr f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Flat.packedDispatcherRegion_mapInstr f profiles hg

theorem packedExecutionRegion_mapInstr :
    packedExecutionRegion (hg.mapInstr profiles) = (packedExecutionRegion hg).mapInstr f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Flat.packedExecutionRegion_mapInstr f profiles hg

end Silmaril.Isotope.LambdaSSA.FiniteCFG
