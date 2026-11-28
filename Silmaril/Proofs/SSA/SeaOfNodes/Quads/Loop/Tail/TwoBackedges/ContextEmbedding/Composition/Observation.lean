module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Transport
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Thms

/-! Soundness through the common native observation on the image of the reduct. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Proofs

open SeaOfNodes.Diamond.SCCP (TupleCovers)
open SeaOfNodes.Loop.MLIR.CF (model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open Identification (PortMap program reduct)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted Backend Sentence SourceReturns)
open Reindex.Guarded.Institution (Generated Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T U : EntrySignature} {result : Width}
variable {first : PortMap S T} {second : Embedding T U}

private theorem staged_eq (pair : Compared first second result) :
    pair.staged = Generated.lower (second.mapAdmitted pair.intermediate.source) := by
  apply Except.ok.inj
  rw [← pair.embedded, second.compile_eq, second.mapGenerated_lower]

theorem source_eq (pair : Compared first second result) :
    @Admitted.source _ _ U.bankEq pair.staged.source = @Admitted.source _ _ U.bankEq pair.direct.source := by
  rw [staged_eq pair]
  change @Admitted.source _ _ U.bankEq (second.mapAdmitted pair.intermediate.source) = _
  rw [embedding_source, Identification.compile_source _ _ pair.identified, program_thenMap]
  exact (Identification.compile_source _ _ pair.composed).symm

theorem staged_coverage (pair : Compared first second result) (input : Valuation U) :
    TupleCovers (@Admitted.facts _ _ U.bankEq pair.staged.source) input ↔
      TupleCovers (@Admitted.facts _ _ S.bankEq pair.source) (reduct (thenMap first second.portMap) input) := by
  rw [staged_eq pair, reduct_embedding]
  exact (second.coverage_iff pair.intermediate.source input).trans
    (Identification.compile_coverage _ _ pair.identified (second.reduct input))

theorem staged_returns (pair : Compared first second result) (backend : Backend)
    (input : Valuation U) (word : Word result) :
    backend.Returns pair.staged.artifacts input word ↔
      SourceReturns (@Admitted.source _ _ S.bankEq pair.source) (reduct (thenMap first second.portMap) input) word := by
  rw [reduct_embedding]
  refine (second.compile_returns_iff backend pair.intermediate.source pair.embedded input word).trans ?_
  simp only [Generated.lower, ← pair.intermediate.generated]
  exact Identification.compile_returns_iff _ _ pair.identified backend (second.reduct input) word

theorem staged_observe (pair : Compared first second result) (backend : Backend) (input : Valuation U) :
    backend.observe pair.staged.artifacts input =
      @Admitted.observe _ _ S.bankEq pair.source (reduct (thenMap first second.portMap) input) := by
  rw [reduct_embedding]
  refine (second.compile_observe backend pair.intermediate.source pair.embedded input).trans ?_
  simp only [Generated.lower, ← pair.intermediate.generated]
  exact Identification.compile_observe _ _ pair.identified backend (second.reduct input)

theorem staged_satisfaction (backend : Backend) (input : Valuation U)
    (sentence : Sentence (Compared first second result)) :
    (sentence.map Compared.staged).Holds (fun q => backend.observe q.artifacts input) ↔
      sentence.Holds (fun q => @Admitted.observe _ _ S.bankEq q.source (reduct (thenMap first second.portMap) input)) := by
  cases sentence <;> simp only [Sentence.map, Sentence.Holds,
    fun q : Compared first second result => staged_observe q backend input]

theorem direct_satisfaction (backend : Backend) (input : Valuation U)
    (sentence : Sentence (Compared first second result)) :
    (sentence.map Compared.direct).Holds (fun q => backend.observe q.artifacts input) ↔
      sentence.Holds (fun q => @Admitted.observe _ _ S.bankEq q.source (reduct (thenMap first second.portMap) input)) := by
  cases sentence <;> simp only [Sentence.map, Sentence.Holds,
    fun q : Compared first second result => Identification.compile_observe _ _ q.composed backend input]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Proofs
