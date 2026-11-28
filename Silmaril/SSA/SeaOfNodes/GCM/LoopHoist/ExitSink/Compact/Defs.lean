module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Defs

/-! # Compact the typed live-in packet of the existing loop exit -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Edge Frame Terminator)
open Silmaril.MLIR.Pure (Operands)
open Loop.MLIR.CF (TargetOp)
open Partition.Discovery (Scan operandIndices)

variable {Input Γ Δ full kept bank results args : List Width}
variable {saved carried result w : Width} {extra : List Width}

/-- An ordered sublist of the original typed exit signature. -/
inductive Projection : List Width → Type where
  | nil : Projection []
  | keep {w : Width} {rest : List Width} : Projection rest → Projection (w :: rest)
  | drop {w : Width} {rest : List Width} : Projection rest → Projection (w :: rest)

def Projection.types : {full : List Width} → Projection full → List Width
  | [], .nil => []
  | w :: _, .keep tail => w :: tail.types
  | _, .drop tail => tail.types

def Projection.indices : {full : List Width} → Projection full → List Nat
  | _, .nil => []
  | _, .keep tail => 0 :: tail.indices.map Nat.succ
  | _, .drop tail => tail.indices.map Nat.succ

def Projection.ofPredicate : (full : List Width) → (Nat → Bool) → Projection full
  | [], _ => .nil
  | _ :: rest, wanted =>
    let tail := ofPredicate rest (fun index => wanted index.succ)
    if wanted 0 then .keep tail else .drop tail

def Projection.forReads (full : List Width) (reads : List Nat) : Projection full :=
  ofPredicate full reads.contains

def Projection.operands : {full : List Width} → (p : Projection full) →
    Operands Γ full → Operands Γ p.types
  | _, .nil, .nil => .nil
  | _, .keep tail, .cons ref rest => .cons ref (tail.operands rest)
  | _, .drop tail, .cons _ rest => tail.operands rest

def Projection.values : {full : List Width} → (p : Projection full) → Env full → Env p.types
  | _, .nil, .nil => .nil
  | _, .keep tail, .cons value rest => .cons value (tail.values rest)
  | _, .drop tail, .cons _ rest => tail.values rest

abbrev PartialRename (Γ Δ : List Width) := ∀ {w}, Var Γ w → Option (Var Δ w)

def keepUnder (rename : PartialRename Γ Δ) : PartialRename (w :: Γ) (w :: Δ)
  | _, .here => some .here
  | _, .there ref => (rename ref).map Var.there

def dropUnder (rename : PartialRename Γ Δ) : PartialRename (w :: Γ) Δ
  | _, .here => none
  | _, .there ref => rename ref

/-- Keep the function inputs after the old packet, while reindexing or
refusing reads of packet arguments. -/
def Projection.rename : {full : List Width} → (p : Projection full) →
    PartialRename (full ++ Input) (p.types ++ Input)
  | _, .nil => fun ref => some ref
  | _, .keep tail => keepUnder tail.rename
  | _, .drop tail => dropUnder tail.rename

def rewriteOperands? (rename : PartialRename Γ Δ) :
    {args : List Width} → Operands Γ args → Option (Operands Δ args)
  | _, .nil => some .nil
  | _, .cons ref rest => do
    let ref ← rename ref
    let rest ← rewriteOperands? rename rest
    pure (.cons ref rest)

/-- Demand only the values needed by the exit return. The existing reverse
let transfer follows dependencies of live producers and marks dead lets. -/
def scanExit? : {Γ : List Width} → Block TargetOp (ExitLabel bank full) Γ results → Option Scan
  | _, .terminator (.ret values) => some ⟨[], operandIndices values⟩
  | _, .terminator _ => none
  | _, .letOp _ operands tail => (scanExit? tail).map (fun scan => scan.beforeBinding operands)

/-- Rewrite the actual exit's lets and return. A true bit drops a pure
binding. Every surviving read must be mapped to a variable of its type. -/
def rewriteExit? : List Bool → {Γ Δ : List Width} → PartialRename Γ Δ →
    Block TargetOp (ExitLabel bank full) Γ results → Option (Block TargetOp (ExitLabel bank kept) Δ results)
  | [], _, _, rename, .terminator (.ret values) =>
    (rewriteOperands? rename values).map (fun reads => .terminator (.ret reads))
  | true :: rest, _, _, rename, .letOp _ _ tail => rewriteExit? rest (dropUnder rename) tail
  | false :: rest, _, _, rename, .letOp op operands tail => do
    let operands ← rewriteOperands? rename operands
    let tail ← rewriteExit? rest (keepUnder rename) tail
    pure (.letOp op operands tail)
  | _, _, _, _, _ => none

def Projection.edge (p : Projection full) : Edge (ExitLabel bank full) Γ → Edge (ExitLabel bank p.types) Γ
  | ⟨.header, packet⟩ => ⟨.header, packet⟩
  | ⟨.exit, packet⟩ => ⟨.exit, p.operands packet⟩

def Projection.term (p : Projection full) :
    Terminator (ExitLabel bank full) results Γ → Terminator (ExitLabel bank p.types) results Γ
  | .br edge => .br (p.edge edge)
  | .condBr guard yes no => .condBr guard (p.edge yes) (p.edge no)
  | .ret values => .ret values

def Projection.frame (p : Projection full) : Frame (ExitLabel bank full) → Frame (ExitLabel bank p.types)
  | ⟨.header, packet⟩ => ⟨.header, packet⟩
  | ⟨.exit, packet⟩ => ⟨.exit, p.values packet⟩

def Projection.target (p : Projection full) : Target (ExitLabel bank full) → Target (ExitLabel bank p.types)
  | ⟨_, .header⟩ => ⟨_, .header⟩
  | ⟨_, .exit⟩ => ⟨_, .exit⟩

/-- Re-read the newly emitted exit to check that every forwarded slot is
needed by its return dependency closure. -/
def packetUsed? (code : Block TargetOp (ExitLabel bank kept) Γ results) : Bool :=
  match scanExit? code with
  | none => false
  | some scan => (List.range kept.length).all scan.inputs.contains

structure Emission (source : TargetCfg Input saved carried result extra full) where
  scan : Scan
  scanned : scanExit? (source.block .exit) = some scan
  exitCode : Block TargetOp (ExitLabel (SavedBank saved carried extra) (Projection.forReads full scan.inputs).types)
    ((Projection.forReads full scan.inputs).types ++ Input) [result]
  rewritten : rewriteExit? scan.mask (Projection.forReads full scan.inputs).rename (source.block .exit) = some exitCode
  covered : packetUsed? exitCode = true

variable {source : TargetCfg Input saved carried result extra full}

def Emission.projection (emission : Emission source) : Projection full :=
  Projection.forReads full emission.scan.inputs

def Emission.cfg (emission : Emission source) :
    TargetCfg Input saved carried result extra emission.projection.types where
  entry := source.entry.mapTerm emission.projection.term
  block
    | .header => (source.block .header).mapTerm emission.projection.term
    | .exit => emission.exitCode

/-- Read and rewrite the emitted CFG itself. A malformed exit or a failed
typed rename returns no artifact. -/
def compact? (source : TargetCfg Input saved carried result extra full) : Option (Emission source) :=
  match scanned : scanExit? (source.block .exit) with
  | none => none
  | some scan =>
    match rewritten : rewriteExit? scan.mask (Projection.forReads full scan.inputs).rename (source.block .exit) with
    | none => none
    | some exitCode =>
      if covered : packetUsed? exitCode then some ⟨scan, scanned, exitCode, rewritten, covered⟩
      else none

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact
