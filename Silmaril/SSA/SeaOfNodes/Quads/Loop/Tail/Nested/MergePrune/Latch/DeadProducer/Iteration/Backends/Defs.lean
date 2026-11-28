module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Defs

/-! # Recognize one nested quad loop and emit both shortened latch targets -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op)
open Silmaril.MLIR.Arith (Width)
open Diamond.Prune (HeaderProjection)
open Nested.Numbered (KeptResult checkResult)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}

inductive Refusal where
  | shape
  | headerProjection
  | mergeProjection
  | splitTransfer
  | resultPort
  deriving DecidableEq, Repr

abbrev carry (p : Program src entry) := Nested.MLIR.CF.carriedMask p
abbrev merge (p : Program src entry) := Latch.mergeMask p (carry p)
abbrev atLatch (p : Program src entry) := Split.latchMask p (carry p)

structure Checked (p : Program src entry) where
  header : HeaderProjection (src p.header).body (carry p)
  split : Split.Checked p (carry p) (merge p) (atLatch p)
  result : KeptResult p (mask := carry p)

/-- Report the first failed check for the recognized program's existing masks. -/
def admit (p : Program src entry) : Except Refusal (Checked p) := do
  let header ← require .headerProjection (Nested.MLIR.CF.prune p)
  let whole ← require .mergeProjection (Latch.prune p (carry p))
  let split ← require .splitTransfer (Split.prepare p whole)
  let result ← require .resultPort (checkResult p (carry p))
  return ⟨header, split, result⟩
where
  require {α : Type} (reason : Refusal) : Option α → Except Refusal α
    | none => .error reason
    | some value => .ok value

/-- Store the two emitted targets and their common checked latch. -/
structure Targets (src : Source Op regs out size) (entry : Fin size) where
  program : Program src entry
  checked : Checked program
  prepared : Prepared checked.split
  cf : MLIR.CF.Target (carry := carry program) (merge := merge program) (atLatch := atLatch program) program
  numbered : RVSDG.NestedTheta.Graph (Join.Opcode Op) (dataPorts regs) []
    ((src entry).body.producers ++ [dataPorts (carry program).kept]) [.value out]
  cf_eq : cf = lowerCF program checked.header checked.split prepared
  numbered_eq : numbered = lowerNumbered program checked.header checked.split prepared checked.result

/-- The same already prepared table also supplies the emitted prefix that
exposes the guard, exit and feedback packet before θ routes it. -/
def Targets.packetRegion (targets : Targets src entry) :=
  (Numbered.DeadProducer.packetWith targets.program targets.checked.header targets.checked.split
    targets.prepared.final).toGraph

/-- The checked entry point runs preparation once and supplies its result
to both emitters. `Except.map` passes any admission error through. -/
def compileChecked (p : Program src entry) : Except Refusal (Targets src entry) :=
  (admit p).map fun checked =>
    let prepared := prepare checked.split
    ⟨p, checked, prepared, lowerCF p checked.header checked.split prepared,
      lowerNumbered p checked.header checked.split prepared checked.result, rfl, rfl⟩

/-- Compile directly from the ordered source table and original entry ID. -/
def compile (src : Source Op regs out size) (entry : Fin size) : Except Refusal (Targets src entry) :=
  match Nested.check src entry with
  | none => .error .shape
  | some p => compileChecked p

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends
