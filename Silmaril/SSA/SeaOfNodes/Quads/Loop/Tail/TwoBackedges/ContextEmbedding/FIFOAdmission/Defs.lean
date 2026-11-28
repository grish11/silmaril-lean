module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Worklist.Thms

/-! Inspect the drained FIFO at a guarded capture-map refusal. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission

open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.Loop.SCCP (bankTuple)
open SeaOfNodes.MLIR (Word)
open Semantics.Dataflow (Flat)
open Silmaril.MLIR.Arith (Width)
open Identification (PortMap checkWrites program pushFacts)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted EntryFacts)
open Reindex.Guarded.Institution (AdmittedAt)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T : EntrySignature} {result : Width}

/-- The exact singleton refusal test on executable feedback occurrences. -/
def Refuses (marks : SCCP.Marked) : SCCP.Dispatch.Refusal → Prop
  | .bothMarked => SCCP.incomingIndex (.feedback true) ∈ marks ∧
      SCCP.incomingIndex (.feedback false) ∈ marks
  | .neitherMarked => SCCP.incomingIndex (.feedback true) ∉ marks ∧
      SCCP.incomingIndex (.feedback false) ∉ marks

/-- The entry facts and actual bounded FIFO run, including its typed bank,
pending queue and visited jobs. The two Boolean facts are post-header reads. -/
structure RefusedRow (T : EntrySignature) (result : Width) where
  facts : EntryFacts T.regs
  run : SCCP.Worklist.Run Word T.regs (.data result)
  continuation : Flat (ULift Bool)
  selector : Flat (ULift Bool)
  reason : SCCP.Dispatch.Refusal

/-- Inspect the same drained marks consumed by the singleton checker.
A single run supplies both the checker and the diagnostic. -/
def inspect (T : EntrySignature) (source : Program Op T.regs (.data result)) (facts : EntryFacts T.regs) :
    Except (RefusedRow T result) Unit :=
  letI := T.bankEq
  let run := SCCP.Worklist.run model source facts
  match SCCP.Dispatch.admitWith model source facts run.state.1
    (congrArg Prod.fst (SCCP.Worklist.solve_eq_simultaneous model source facts)) with
  | .ok _ => .ok ()
  | .error reason =>
    let header := SCCP.blockFacts model source.header (bankTuple run.state.2.1)
    .error ⟨facts, run, header.get source.again, header.get source.select, reason⟩

inductive Refusal (T : EntrySignature) (result : Width) where
  | aliasedWrite
  | incompatibleFacts
  | fifo (row : RefusedRow T result)

def Refusal.reason : Refusal T result → Identification.Refusal
  | .aliasedWrite => .aliasedWrite
  | .incompatibleFacts => .incompatibleFacts
  | .fifo row => .checker row.reason

/-- Diagnose a guarded compiler call without emitting target code. The FIFO
runs only after the write check and typed fact intersection succeed. -/
def diagnose (map : PortMap S T) (seed : AdmittedAt S result) : Except (Refusal T result) Unit :=
  let source := @Admitted.source _ _ S.bankEq seed
  if checkWrites map source then
    match pushFacts map (@Admitted.facts _ _ S.bankEq seed) with
    | none => .error .incompatibleFacts
    | some facts => (inspect T (program map source) facts).mapError Refusal.fifo
  else .error .aliasedWrite

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission
