module

public import Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.EarlyPlacement.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open Dominance (checkClosed)
open LatePlacement (lateBound?)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result} {tree : DominatorTree cfg}
variable {operands : List (Point Label)} {early : BlockId Label}

/-- A reachable block is dominated by the early bound exactly when it is
dominated by all the valid operand definition blocks. -/
theorem earlyBound?_spec (complete : tree.Complete)
    (found : earlyBound? tree operands = some early) :
    Reachable cfg early ∧ (∀ operand ∈ operands, operand.Valid cfg) ∧
      ∀ block, Reachable cfg block →
        (Dominates cfg early block ↔ ∀ operand ∈ operands, Dominates cfg operand.block block) :=
  Proofs.SSA.SeaOfNodes.GCM.EarlyPlacement.earlyBound?_spec complete found

/-- An early bound exists exactly when all definition cuts are valid and the
definition blocks have a common reachable dominated block. -/
theorem earlyBound?_isSome_iff (complete : tree.Complete) :
    (earlyBound? tree operands).isSome = true ↔
      (∀ operand ∈ operands, operand.Valid cfg) ∧
        ∃ block, Reachable cfg block ∧ ∀ operand ∈ operands, Dominates cfg operand.block block :=
  Proofs.SSA.SeaOfNodes.GCM.EarlyPlacement.earlyBound?_isSome_iff complete

variable [DecidableEq (Target Label)]
variable {blocks : List (Target Label)} {uses : List (Use Label)}
variable {late : BlockId Label} {candidate : Point Label}

/-- The two block bounds characterize the control corridor of the existing
checker. Operand and read order still constrain cuts within a block. -/
theorem legal_iff_bounds (complete : tree.Complete) (closed : checkClosed cfg blocks = true)
    (earlyFound : earlyBound? tree operands = some early)
    (lateFound : lateBound? tree blocks uses = some late) :
    Legal cfg operands uses candidate ↔
      candidate.Valid cfg ∧ Dominates cfg early candidate.block ∧
      Dominates cfg candidate.block late ∧
      (∀ operand ∈ operands, operand.block = candidate.block → operand.cut ≤ candidate.cut) ∧
      ∀ use ∈ uses, ∀ read, use.point? cfg = some read →
        candidate.block = read.block → candidate.cut ≤ read.cut :=
  Proofs.SSA.SeaOfNodes.GCM.EarlyPlacement.legal_iff_bounds complete closed earlyFound lateFound

/-- A legal cut requires the early bound to dominate the late bound. -/
theorem early_dominates_late_of_legal (complete : tree.Complete)
    (closed : checkClosed cfg blocks = true)
    (earlyFound : earlyBound? tree operands = some early)
    (lateFound : lateBound? tree blocks uses = some late)
    (legal : Legal cfg operands uses candidate) : Dominates cfg early late :=
  Proofs.SSA.SeaOfNodes.GCM.EarlyPlacement.early_dominates_late_of_legal
    complete closed earlyFound lateFound legal

end Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement
