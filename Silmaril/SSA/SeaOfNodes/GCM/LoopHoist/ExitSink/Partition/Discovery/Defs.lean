module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Defs

/-! # Discover exit moves from the typed guard and feedback dependency closure -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Block Terminator)
open Silmaril.MLIR.Pure (Operands)
open Loop.MLIR.CF (TargetOp)

variable {Input extra Γ : List Width} {saved carried result : Width}

/-- Read the actual typed operand indices in packet order, including repetitions. -/
def operandIndices : {args : List Width} → Operands Γ args → List Nat
  | _, .nil => []
  | _, .cons ref tail => ref.index :: operandIndices tail

/-- The guard and every argument of the actual true-edge feedback are
roots. The false-edge result is left to the exit placement checker. -/
def roots? : Terminator (Label saved carried result extra) [result] Γ → Option (List Nat)
  | .condBr guard ⟨.header, feedback⟩ ⟨.exit, _⟩ =>
    some (guard.index :: operandIndices feedback)
  | _ => none

/-- Convert surviving reads from the scope after a let to the scope before
it. Index zero is handled at the binding that defines it. -/
def older (reads : List Nat) : List Nat :=
  reads.filterMap fun
    | 0 => none
    | index + 1 => some index

structure Scan where
  mask : List Bool
  inputs : List Nat
  deriving BEq, Repr

def Scan.beforeBinding {args : List Width} (tail : Scan) (operands : Operands Γ args) : Scan :=
  if 0 ∈ tail.inputs then
    ⟨false :: tail.mask, older tail.inputs ++ operandIndices operands⟩
  else
    ⟨true :: tail.mask, older tail.inputs⟩

/-- Scan the lets backwards and emit the complement of the required set
in input-header order. The carried reads are indices in the current scope. -/
def scan? : {Γ : List Width} →
    Block TargetOp (Label saved carried result extra) Γ [result] → Option Scan
  | _, .terminator term => (roots? term).map (⟨[], ·⟩)
  | _, .letOp _ operands tail => (scan? tail).map (fun scan => scan.beforeBinding operands)

/-- Declarative control closure for a caller's placement mask. A retained
let must provide its operand reads to earlier definitions. A moved let
cannot discharge any read from retained code, the guard, or feedback. -/
inductive RetainedReads : {Γ : List Width} →
    Block TargetOp (Label saved carried result extra) Γ [result] → List Bool → List Nat → Prop where
  | finish {Γ : List Width} {term : Terminator (Label saved carried result extra) [result] Γ}
      {reads : List Nat} (root : roots? term = some reads) :
      RetainedReads (.terminator term) [] reads
  | keep {Γ args : List Width} {w : Width} {op : TargetOp args w} {operands : Operands Γ args}
      {tail : Block TargetOp (Label saved carried result extra) (w :: Γ) [result]}
      {mask : List Bool} {reads : List Nat} (valid : RetainedReads tail mask reads) :
      RetainedReads (.letOp op operands tail) (false :: mask) (older reads ++ operandIndices operands)
  | move {Γ args : List Width} {w : Width} {op : TargetOp args w} {operands : Operands Γ args}
      {tail : Block TargetOp (Label saved carried result extra) (w :: Γ) [result]}
      {mask : List Bool} {reads : List Nat} (valid : RetainedReads tail mask reads) (unused : 0 ∉ reads) :
      RetainedReads (.letOp op operands tail) (true :: mask) (older reads)

inductive Refusal where
  | controlShape
  | noMove
  | partition
  deriving DecidableEq, Repr

structure Plan (source : Source Input saved carried result extra) where
  scan : Scan
  scanned : scan? (source.block .header) = some scan
  emission : Partition.Emission source scan.mask
  checked : Partition.sink? source scan.mask = some emission

variable {source : Source Input saved carried result extra}

abbrev Plan.cfg (plan : Plan source) := plan.emission.cfg

/-- Derive a proposal from the current CFG, then use the existing typed
partition check and its emitted artifact. An error carries no CFG. -/
def discover (source : Source Input saved carried result extra) : Except Refusal (Plan source) :=
  match scanned : scan? (source.block .header) with
  | none => .error .controlShape
  | some scan =>
    if scan.mask.contains true then
      match checked : Partition.sink? source scan.mask with
      | none => .error .partition
      | some emission => .ok ⟨scan, scanned, emission, checked⟩
    else .error .noMove

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery
