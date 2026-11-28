module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Defs

/-! # One checked follow-on placement on a permuted saved prefix -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (Operands)
open AfterReorder.Second (Candidate)
open Loop.MLIR.CF (TargetOp)

variable {Input extra : List Width} {saved carried result : Width}

abbrev CurrentExtra (prior : Earlier.Emission Input saved carried result extra) :=
  prior.append.candidate.width :: extra

/-- Reuse the earlier emission's actual prefix and typed slot map. -/
def toLayout (prior : Earlier.Emission Input saved carried result extra) :
    Layout.State Input saved carried result (CurrentExtra prior) :=
  ⟨prior.append.next, prior.splice.physical, prior.splice.leading, prior.entryTail, prior.splice.toPhysical⟩

def savedCount (prior : Earlier.Emission Input saved carried result extra) : Nat :=
  (toLayout prior).savedCount

abbrev physicalSites {Γ : List Width} (count : Nat) : {args : List Width} → Operands Γ args →
    List (Point (Label saved carried result extra)) :=
  Layout.physicalSites count

def physicalOperands (prior : Earlier.Emission Input saved carried result extra)
    (candidate : Candidate Input saved carried result (CurrentExtra prior)) :
    Operands prior.splice.physical candidate.args :=
  (toLayout prior).physicalOperands candidate

def atLayout (prior : Earlier.Emission Input saved carried result extra)
    (candidate : Candidate Input saved carried result (CurrentExtra prior)) :
    Candidate Input saved carried result (CurrentExtra prior) :=
  (toLayout prior).atLayout candidate

structure Emission (prior : Earlier.Emission Input saved carried result extra) where
  append : Step.Emission Input saved carried result (CurrentExtra prior)
  splice : Saved.Prefix.Insertion Input prior.splice.physical append.candidate.width

def Emission.toMove {prior : Earlier.Emission Input saved carried result extra} (moved : Emission prior) :
    Layout.Move (toLayout prior) :=
  ⟨moved.append, moved.splice⟩

def Emission.cfg {prior : Earlier.Emission Input saved carried result extra} (moved : Emission prior) :
    Cfg TargetOp (Label saved carried result (moved.append.candidate.width :: CurrentExtra prior)) Input [result] :=
  moved.toMove.next.cfg

/-- The single follow-on interface uses the same checked transition as finite replay. -/
def emit? (prior : Earlier.Emission Input saved carried result extra) (request : Nomination) :
    Option (Emission prior) :=
  (Layout.emit? (toLayout prior) request).map fun moved => ⟨moved.append, moved.splice⟩

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow
