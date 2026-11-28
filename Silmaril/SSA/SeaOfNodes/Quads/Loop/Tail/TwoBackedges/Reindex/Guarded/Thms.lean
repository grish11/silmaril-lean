module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Admission
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Correctness

/-! The actual re-emitted artifacts commute with reduction of the typed entry valuation. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded

open CategoryTheory Silmaril.Logic.Institution
open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.SCCP (BankDecidableEq decideTupleCovers)
open SeaOfNodes.Loop.MLIR.CF (model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open Tail.Diamond.MLIR.CF.Pruned.Reindex (pull)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution
  (Admitted admit Backend Entry EntryFacts Sentence SourceReturns sourceRoom targetRoom comparison)

open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard (entry entry_eval)
open SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard (selector selector_run)

universe u v w

/-- Every singleton certificate is recovered by the existing FIFO checker. -/
theorem fifo_accepts {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
    {regs : List (ValueSort Data)} {result : ValueSort Data}
    {m : SeaOfNodes.Diamond.Model.{u, v, w} Op}
    [BankDecidableEq m.value (dataPorts regs)]
    {source : Program Op regs result}
    {facts : RVSDG.Tuple (SeaOfNodes.Diamond.SCCP.Fact m.value) (dataPorts regs)}
    (cert : SCCP.Dispatch.Checked m source facts) :
    SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.admit m source facts = .ok cert :=
  Proofs.fifo_accepts cert

variable {old new : List (ValueSort Width)} {result : Width}
variable [BankDecidableEq Word (dataPorts old)] [BankDecidableEq Word (dataPorts new)]
variable (order : Registers old new)

theorem admit_reindex (p : Admitted old result) :
    admit (program order p.source) (push order p.facts) = .ok (reindex order p) :=
  Proofs.admit_reindex order p

theorem coverage_decision (facts : EntryFacts old) (input : Entry new) :
    @decide _ (decideTupleCovers (push order facts) input) =
      @decide _ (decideTupleCovers facts (pull order input)) :=
  decide_eq_decide.mpr (covers_iff order facts input)

/-- The emitted CF entry takes the same empty-argument edge at the reduced input. -/
theorem cf_guard {Labels : List Width → Type} {Result : List Width} (accept reject : Labels [])
    (facts : EntryFacts old) (input : Entry new) :
    (entry (Result := Result) (push order facts) accept reject).eval evalOp
        (fun term env => term.eval env) (encodeValues input) =
      (entry (Result := Result) facts accept reject).eval evalOp
        (fun term env => term.eval env) (encodeValues (pull order input)) := by
  simp only [entry_eval, coverage_decision]

/-- The actual numbered selector passes the same γ tag at the reduced input. -/
theorem numbered_guard (facts : EntryFacts old) (input : Entry new) :
    (selector (push order facts)).2.toGraph.run (Join.model model) input =
      (selector facts).2.toGraph.run (Join.model model) (pull order input) := by
  simp only [selector_run, coverage_decision]

/-- The native partial result includes the absence of any finite return. -/
theorem source_observe (p : Admitted old result) (input : Entry new) :
    (reindex order p).observe input = p.observe (pull order input) :=
  Part.ext fun word => ((reindex order p).mem_observe_iff input word).trans
    ((show SourceReturns (program order p.source) input word ↔
      SourceReturns p.source (pull order input) word by simp only [SourceReturns, source_run]).trans
      (p.mem_observe_iff _ _).symm)

/-- Quantify finite witnesses independently in the two re-emissions. -/
theorem backend_returns (backend : Backend) (p : Admitted old result) (input : Entry new) (word : Word result) :
    backend.Returns (reindex order p).emit input word ↔ backend.Returns p.emit (pull order input) word := by
  rw [← backend.mem_observe_iff, ← backend.mem_observe_iff,
    backend.observe_eq_source, backend.observe_eq_source, source_observe]

theorem backend_observe (backend : Backend) (p : Admitted old result) (input : Entry new) :
    backend.observe (reindex order p).emit input = backend.observe p.emit (pull order input) := by
  rw [backend.observe_eq_source, backend.observe_eq_source, source_observe]

theorem source_satisfaction (input : Entry new) (sentence : Sentence (Admitted old result)) :
    (sentence.map (reindex order)).Holds (fun p => p.observe input) ↔
      sentence.Holds (fun p => p.observe (pull order input)) := by
  cases sentence <;> simp only [Sentence.map, Sentence.Holds, source_observe]

/-- Source sentences are renamed forward, and target valuations reduce backward. -/
noncomputable def sourceCorridor : sourceRoom old result ⟶ sourceRoom new result :=
  ⟨Sentence.map (reindex order), Discrete.functor (fun input : Entry new => Discrete.mk (pull order input)),
    fun m s => source_satisfaction order m.as s⟩

/-- Equation and termination satisfaction commute with re-emission and valuation reduction
for each actual backend generated from an admitted source. -/
theorem backend_satisfaction (backend : Backend) (input : Entry new)
    (sentence : Sentence (Admitted old result)) :
    (targetRoom new result backend).Sat (Discrete.mk input)
      ((comparison backend).sen ((sourceCorridor order).sen sentence)) ↔
    (targetRoom old result backend).Sat (Discrete.mk (pull order input)) ((comparison backend).sen sentence) :=
  ((comparison backend).sat _ _).trans
    ((source_satisfaction order input sentence).trans ((comparison backend).sat _ _).symm)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded
