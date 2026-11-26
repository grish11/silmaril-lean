module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Thms

/-! Guard selection and partial observations commute with forgetting the fresh capture. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded

open CategoryTheory Silmaril.Logic.Institution
open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.SCCP (decideTupleCovers)
open SeaOfNodes.Loop.MLIR.CF (model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open SCCP.Dispatch (Checked)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard (entry entry_eval)
open SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard (selector selector_run)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution
  (Admitted Backend EntryFacts Sentence SourceReturns)
open Reindex.Guarded.Institution
  (AdmittedAt Generated Valuation nativeRoom generatedRoom emitCorridor)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S : EntrySignature} {result : Width} (fresh : ValueSort Width)

theorem replay_eq (p : AdmittedAt S result) : replay fresh p = .ok (lift fresh p) :=
  @Admitted.admit_self _ _ (extend S fresh).bankEq (lift fresh p)

theorem compile_eq (p : AdmittedAt S result) :
    compile fresh p = .ok (Generated.lower (lift fresh p)) :=
  congrArg (Except.map Generated.lower) (replay_eq fresh p)

theorem selected_side (p : AdmittedAt S result) :
    @Checked.side _ _ _ _ model _ (extend S fresh).bankEq _
      (@Admitted.checked _ _ (extend S fresh).bankEq (lift fresh p)) =
    @Checked.side _ _ _ _ model _ S.bankEq _ (@Admitted.checked _ _ S.bankEq p) := rfl

theorem coverage_decision (contract : EntryFacts S.regs) (input : Valuation (extend S fresh)) :
    @decide _ (@decideTupleCovers _ _ _ (extend S fresh).bankEq (facts fresh contract) input) =
      @decide _ (@decideTupleCovers _ _ _ S.bankEq contract (project input)) :=
  decide_eq_decide.mpr (covers_iff contract input)

/-- The actual emitted CF guard takes the same empty-argument edge. -/
theorem cf_guard {Labels : List Width → Type} {Result : List Width} (accept reject : Labels [])
    (contract : EntryFacts S.regs) (input : Valuation (extend S fresh)) :
    (entry (Result := Result) (facts fresh contract) accept reject).eval evalOp
        (fun term env => term.eval env) (encodeValues input) =
      (entry (Result := Result) contract accept reject).eval evalOp
        (fun term env => term.eval env) (encodeValues (project input)) := by
  refine (@entry_eval _ (extend S fresh).bankEq Labels Result accept reject (facts fresh contract) input).trans ?_
  rw [coverage_decision fresh contract input]
  exact (@entry_eval _ S.bankEq Labels Result accept reject contract (project input)).symm

/-- The emitted selector chooses the same γ arm for any fresh value. -/
theorem numbered_guard (contract : EntryFacts S.regs) (input : Valuation (extend S fresh)) :
    (selector (facts fresh contract)).2.toGraph.run (Join.model model) input =
      (selector contract).2.toGraph.run (Join.model model) (project input) := by
  refine (@selector_run _ (extend S fresh).bankEq (facts fresh contract) input).trans ?_
  rw [coverage_decision fresh contract input]
  exact (@selector_run _ S.bankEq contract (project input)).symm

theorem source_returns (p : AdmittedAt S result) (input : Valuation (extend S fresh)) (word : Word result) :
    SourceReturns (@Admitted.source _ _ (extend S fresh).bankEq (lift fresh p)) input word ↔
      SourceReturns (@Admitted.source _ _ S.bankEq p) (project input) word := by
  change SourceReturns (program fresh (@Admitted.source _ _ S.bankEq p)) input word ↔ _
  exact exists_congr fun fuel => Iff.of_eq
    (congrArg (fun observation => observation = some word)
      (Weakening.source_run model (@Admitted.source _ _ S.bankEq p) fuel input))

theorem native_observe (p : AdmittedAt S result) (input : Valuation (extend S fresh)) :
    @Admitted.observe _ _ (extend S fresh).bankEq (lift fresh p) input =
      @Admitted.observe _ _ S.bankEq p (project input) :=
  Part.ext fun word => (@Admitted.mem_observe_iff _ _ (extend S fresh).bankEq (lift fresh p) input word).trans
    ((source_returns fresh p input word).trans (@Admitted.mem_observe_iff _ _ S.bankEq p (project input) word).symm)

/-- The old and enlarged artifacts have independent finite witnesses for each exact word. -/
theorem backend_returns (backend : Backend) (p : Generated S result)
    (input : Valuation (extend S fresh)) (word : Word result) :
    backend.Returns (liftGenerated fresh p).artifacts input word ↔
      backend.Returns p.artifacts (project input) word := by
  rw [p.generated]
  exact (@Backend.returns_iff_source _ _ (extend S fresh).bankEq backend (lift fresh p.source) input word).trans
    ((source_returns fresh p.source input word).trans
      (@Backend.returns_iff_source _ _ S.bankEq backend p.source (project input) word).symm)

theorem compile_returns_iff (backend : Backend) (p : AdmittedAt S result)
    {target : Generated (extend S fresh) result} (success : compile fresh p = .ok target)
    (input : Valuation (extend S fresh)) (word : Word result) :
    backend.Returns target.artifacts input word ↔
      SourceReturns (@Admitted.source _ _ S.bankEq p) (project input) word := by
  cases Except.ok.inj ((compile_eq fresh p).symm.trans success)
  exact (backend_returns fresh backend (Generated.lower p) input word).trans
    (@Backend.returns_iff_source _ _ S.bankEq backend p (project input) word)

theorem backend_noReturn (backend : Backend) (p : Generated S result)
    (input : Valuation (extend S fresh)) :
    (¬ ∃ word, backend.Returns (liftGenerated fresh p).artifacts input word) ↔
      ¬ ∃ word, backend.Returns p.artifacts (project input) word :=
  not_congr (exists_congr (backend_returns fresh backend p input))

theorem backend_observe (backend : Backend) (p : Generated S result) (input : Valuation (extend S fresh)) :
    backend.observe (liftGenerated fresh p).artifacts input = backend.observe p.artifacts (project input) :=
  Part.ext fun word => (backend.mem_observe_iff ..).trans
    ((backend_returns fresh backend p input word).trans (backend.mem_observe_iff ..).symm)

/-- Translate native equations and termination forward, dropping the capture from valuations. -/
noncomputable def nativeCorridor : nativeRoom result S ⟶ nativeRoom result (extend S fresh) :=
  ⟨Sentence.map (lift fresh), Discrete.functor
    (fun input : Valuation (extend S fresh) => Discrete.mk (project input)),
    fun input sentence => by
      change (sentence.map (lift fresh)).Holds
          (fun p => @Admitted.observe _ _ (extend S fresh).bankEq p input.as) ↔
        sentence.Holds (fun p => @Admitted.observe _ _ S.bankEq p (project input.as))
      cases sentence <;> simp only [Sentence.map, Sentence.Holds, native_observe]⟩

/-- The same valuation reduct applies to sentences about the actual generated artifacts. -/
noncomputable def generatedCorridor (backend : Backend) :
    generatedRoom result backend S ⟶ generatedRoom result backend (extend S fresh) :=
  ⟨Sentence.map (liftGenerated fresh), (nativeCorridor (S := S) (result := result) fresh).mod,
    fun input sentence => by
      change (sentence.map (liftGenerated fresh)).Holds (fun p => backend.observe p.artifacts input.as) ↔
        sentence.Holds (fun p => backend.observe p.artifacts (project input.as))
      cases sentence <;> simp only [Sentence.map, Sentence.Holds, backend_observe]⟩

/-- The local weakening square uses #4470's emission comparison at each endpoint. -/
theorem emit_commutes (backend : Backend) :
    nativeCorridor (result := result) fresh ≫ emitCorridor backend (extend S fresh) =
      emitCorridor backend S ≫ generatedCorridor fresh backend :=
  Room.hom_ext (funext fun sentence => by cases sentence <;> rfl)
    (Discrete.functor_ext fun _ => rfl)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded
