module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Diagnostic
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Refinement
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Compiler

/-! Checked refusal diagnostics and the write-safe first-stage obstruction. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Diamond.SCCP (TupleLE)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.Loop.SCCP (bankTuple)
open Silmaril.MLIR.Arith (Width)
open Composition (thenMap)
open Identification (PortMap SafeWrites checkWrites program pull pushFacts)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted EntryFacts admit)
open Reindex.Guarded.Institution (AdmittedAt)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T U : EntrySignature} {result : Width} {out : ValueSort Width}

/-- Erase the extra diagnostic data to recover the actual compiler outcome. -/
theorem diagnose_compile (map : PortMap S T) (seed : AdmittedAt S result) :
    (diagnose map seed).mapError Refusal.reason = (Identification.compile map seed).map (fun _ => ()) :=
  Proofs.diagnose_compile map seed

/-- A FIFO diagnostic requires both structural checks to have reached the solver. -/
theorem fifo_of_diagnose (map : PortMap S T) (seed : AdmittedAt S result)
    (row : RefusedRow T result) (ran : diagnose map seed = .error (.fifo row)) :
    checkWrites map (@Admitted.source _ _ S.bankEq seed) = true ∧
      pushFacts map (@Admitted.facts _ _ S.bankEq seed) = some row.facts ∧
      inspect T (program map (@Admitted.source _ _ S.bankEq seed)) row.facts = .error row :=
  Proofs.fifo_of_diagnose map seed row ran

/-- The witness is the exact bounded FIFO run, with an empty pending queue. -/
theorem inspect_row (source : Program Op T.regs (.data result)) (facts : EntryFacts T.regs)
    (row : RefusedRow T result) (found : inspect T source facts = .error row) :
    row.run = @SCCP.Worklist.run _ _ _ _ model source T.bankEq facts ∧ row.run.pending = [] ∧
      row.continuation = (SCCP.blockFacts model source.header (bankTuple row.run.state.2.1)).get source.again ∧
      row.selector = (SCCP.blockFacts model source.header (bankTuple row.run.state.2.1)).get source.select ∧
      Refuses row.run.state.1 row.reason :=
  Proofs.inspect_row source facts row found

/-- The guard admits exactly one of the two feedback occurrences. -/
theorem admit_refusal_iff (code : Program Op T.regs (.data result)) (facts : EntryFacts T.regs)
    (reason : SCCP.Dispatch.Refusal) :
    @admit _ _ T.bankEq code facts = .error reason ↔
      Refuses (@SCCP.Worklist.solve _ _ _ _ model code T.bankEq facts).1 reason :=
  Proofs.admit_refusal_iff code facts reason

/-- A compiler checker refusal follows successful write and fact checks. -/
theorem compile_checker_iff (map : PortMap S T) (seed : AdmittedAt S result)
    (reason : SCCP.Dispatch.Refusal) : Identification.compile map seed = .error (.checker reason) ↔
    checkWrites map (@Admitted.source _ _ S.bankEq seed) = true ∧
      ∃ facts, pushFacts map (@Admitted.facts _ _ S.bankEq seed) = some facts ∧
        Refuses (@SCCP.Worklist.solve _ _ _ _ model
          (program map (@Admitted.source _ _ S.bankEq seed)) T.bankEq facts).1 reason :=
  Proofs.compile_checker_iff map seed reason

/-- A write-safe map with refining entry facts can only remove occurrence marks. -/
theorem fifo_marks_subset (map : PortMap S T) (p : Program Op S.regs out)
    (safe : SafeWrites map p) (original : EntryFacts S.regs) (mapped : EntryFacts T.regs)
    (entry : TupleLE (pull map mapped) original) :
    (@SCCP.Worklist.solve _ _ _ _ model (program map p) T.bankEq mapped).1 ⊆
      (@SCCP.Worklist.solve _ _ _ _ model p S.bankEq original).1 :=
  Proofs.fifo_marks_subset map p safe original mapped entry

/-- An admitted seed cannot gain a second feedback mark through checked capture transport. -/
theorem compile_never_both (map : PortMap S T) (seed : AdmittedAt S result) :
    Identification.compile map seed ≠ .error (.checker .bothMarked) :=
  Proofs.compile_never_both map seed

/-- After a first FIFO refusal, a write-safe suffix reports the same refusal
or an incompatible final fact intersection. -/
theorem direct_of_neither (first : PortMap S T) (second : PortMap T U) (seed : AdmittedAt S result)
    (refused : Identification.compile first seed = .error (.checker .neitherMarked))
    (writeSafe : checkWrites second (program first (@Admitted.source _ _ S.bankEq seed)) = true) :
    Identification.compile (thenMap first second) seed =
      match pushFacts (thenMap first second) (@Admitted.facts _ _ S.bankEq seed) with
      | none => .error .incompatibleFacts
      | some _ => .error (.checker .neitherMarked) :=
  Proofs.direct_of_neither first second seed refused writeSafe

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission
