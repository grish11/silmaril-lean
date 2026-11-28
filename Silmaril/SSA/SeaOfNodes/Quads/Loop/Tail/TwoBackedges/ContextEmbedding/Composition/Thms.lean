module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Transport
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Checks
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Observation

/-! Composed port maps preserve the covered inputs and partial observations
of successful staged and direct compilations. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (TupleCovers)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Tuple)
open Blocks (Bank)
open Identification (BankMap PortMap pull reduct program SafeWrites checkWrites pushFacts)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted Backend EntryFacts Sentence SourceReturns admit)
open Reindex.Guarded.Institution (AdmittedAt Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {old middle new final : List (ValueSort Width)} {out : ValueSort Width}
variable {S T U V : EntrySignature} {result : Width}

theorem thenMap_assoc (a : BankMap old middle) (b : BankMap middle new) (c : BankMap new final) :
    thenMap (thenMap a b) c = thenMap a (thenMap b c) := rfl

theorem thenMap_embeddings (map : PortMap S T) (first : Embedding T U) (second : Embedding U V) :
    thenMap map (first.trans second).portMap = thenMap (thenMap map first.portMap) second.portMap := by
  funext sort port
  exact first.portMap_trans second (map sort port)

theorem pull_thenMap {F : SeaOfNodes.Diamond.Ty Width → Type}
    (first : BankMap old middle) (second : BankMap middle new) (input : Tuple F (dataPorts new)) :
    pull (thenMap first second) input = pull first (pull second input) :=
  Proofs.pull_thenMap first second input

theorem reduct_thenMap (first : PortMap S T) (second : PortMap T U) (input : Valuation U) :
    reduct (thenMap first second) input = reduct first (reduct second input) :=
  pull_thenMap first second input

theorem reduct_embedding (first : PortMap S T) (second : Embedding T U) (input : Valuation U) :
    reduct (thenMap first second.portMap) input = reduct first (second.reduct input) :=
  Proofs.reduct_embedding first second input

/-- Composition transports the actual ordered writes and typed terminator ports. -/
theorem program_thenMap (first : BankMap old middle) (second : BankMap middle new)
    (p : Program Op old out) :
    program second (program first p) = program (thenMap first second) p :=
  Proofs.program_thenMap first second p

theorem program_identity (p : Program Op old out) : program (fun _ port => port) p = p :=
  Proofs.program_identity p

theorem embedding_source (path : Embedding S T) (p : AdmittedAt S result) :
    @Admitted.source _ _ T.bankEq (path.mapAdmitted p) =
      program path.portMap (@Admitted.source _ _ S.bankEq p) :=
  Proofs.embedding_source path p

theorem safeWrites_of_thenMap (first : BankMap old middle) (second : BankMap middle new)
    (p : Program Op old out) (safe : SafeWrites (thenMap first second) p) : SafeWrites first p :=
  Proofs.safeWrites_of_thenMap first second p safe

theorem safeWrites_thenMap (first : BankMap old middle) (second : BankMap middle new)
    (p : Program Op old out) (firstSafe : SafeWrites first p)
    (secondSafe : SafeWrites second (program first p)) : SafeWrites (thenMap first second) p :=
  Proofs.safeWrites_thenMap first second p firstSafe secondSafe

/-- An embedding after identification leaves the singleton-write-preimage check unchanged. -/
theorem checkWrites_embedding (first : PortMap S T) (second : Embedding T U) (p : Program Op S.regs out) :
    checkWrites (thenMap first second.portMap) p = checkWrites first p :=
  Proofs.checkWrites_embedding first second p

/-- Fact intersection agrees at every final valuation, treating a refused intersection as empty. -/
theorem pushFacts_thenMap (first : BankMap old middle) (second : BankMap middle new)
    (facts : EntryFacts old) (input : Bank (regs := new) model) :
    (∃ direct, pushFacts (thenMap first second) facts = some direct ∧ TupleCovers direct input) ↔
      (∃ intermediate final, pushFacts first facts = some intermediate ∧
        pushFacts second intermediate = some final ∧ TupleCovers final input) :=
  Proofs.pushFacts_thenMap first second facts input

/-- A staged refusal is exactly the intermediate refusal because embedding replay is total on admitted inputs. -/
theorem compileStaged_error_iff (first : PortMap S T) (second : Embedding T U)
    (p : AdmittedAt S result) (reason : Identification.Refusal) :
    compileStaged first second p = .error reason ↔ Identification.compile first p = .error reason :=
  Proofs.compileStaged_error_iff first second p reason

/-- A FIFO refusal certifies that the intermediate write and fact checks passed. -/
theorem compileStaged_checker_iff (first : PortMap S T) (second : Embedding T U)
    (p : AdmittedAt S result) (reason : SCCP.Dispatch.Refusal) :
    compileStaged first second p = .error (.checker reason) ↔
      checkWrites first (@Admitted.source _ _ S.bankEq p) = true ∧
        ∃ facts, pushFacts first (@Admitted.facts _ _ S.bankEq p) = some facts ∧
          @admit _ _ T.bankEq (program first (@Admitted.source _ _ S.bankEq p)) facts = .error reason :=
  Proofs.compileStaged_checker_iff first second p reason

namespace Compared

variable {first : PortMap S T} {second : Embedding T U}

theorem staged_compiled (pair : Compared first second result) :
    compileStaged first second pair.source = .ok pair.staged := by
  simp [compileStaged, pair.identified, pair.embedded, Except.mapError]

theorem source_eq (pair : Compared first second result) :
    @Admitted.source _ _ U.bankEq pair.staged.source = @Admitted.source _ _ U.bankEq pair.direct.source :=
  Proofs.source_eq pair

/-- Both native programs agree with the original at each source block budget. -/
theorem native_run (pair : Compared first second result) (fuel : Nat) (input : Valuation U) :
    (@Admitted.source _ _ U.bankEq pair.staged.source).source.runFrom model fuel 0 input =
      (@Admitted.source _ _ S.bankEq pair.source).source.runFrom model fuel 0
        (reduct (thenMap first second.portMap) input) := by
  rw [pair.source_eq]
  exact Identification.compile_native_run _ _ pair.composed fuel input

theorem staged_coverage (pair : Compared first second result) (input : Valuation U) :
    TupleCovers (@Admitted.facts _ _ U.bankEq pair.staged.source) input ↔
      TupleCovers (@Admitted.facts _ _ S.bankEq pair.source) (reduct (thenMap first second.portMap) input) :=
  Proofs.staged_coverage pair input

theorem coverage_iff (pair : Compared first second result) (input : Valuation U) :
    TupleCovers (@Admitted.facts _ _ U.bankEq pair.staged.source) input ↔
      TupleCovers (@Admitted.facts _ _ U.bankEq pair.direct.source) input :=
  (pair.staged_coverage input).trans (Identification.compile_coverage _ _ pair.composed input).symm

/-- Compare actual emissions with independent CF, numbered, or Petri witnesses. -/
theorem staged_returns (pair : Compared first second result) (backend : Backend)
    (input : Valuation U) (word : Word result) :
    backend.Returns pair.staged.artifacts input word ↔
      SourceReturns (@Admitted.source _ _ S.bankEq pair.source)
        (reduct (thenMap first second.portMap) input) word :=
  Proofs.staged_returns pair backend input word

theorem returns_iff (pair : Compared first second result) (backend : Backend)
    (input : Valuation U) (word : Word result) :
    backend.Returns pair.staged.artifacts input word ↔ backend.Returns pair.direct.artifacts input word :=
  (pair.staged_returns backend input word).trans
    (Identification.compile_returns_iff _ _ pair.composed backend input word).symm

theorem noReturn_iff (pair : Compared first second result) (backend : Backend) (input : Valuation U) :
    (¬ ∃ word, backend.Returns pair.staged.artifacts input word) ↔
      ¬ ∃ word, backend.Returns pair.direct.artifacts input word :=
  not_congr (exists_congr (pair.returns_iff backend input))

theorem observe_eq (pair : Compared first second result) (backend : Backend) (input : Valuation U) :
    backend.observe pair.staged.artifacts input = backend.observe pair.direct.artifacts input :=
  (Proofs.staged_observe pair backend input).trans
    (Identification.compile_observe _ _ pair.composed backend input).symm

theorem staged_satisfaction (backend : Backend) (input : Valuation U)
    (sentence : Sentence (Compared first second result)) :
    (sentence.map Compared.staged).Holds (fun q => backend.observe q.artifacts input) ↔
      sentence.Holds (fun q => @Admitted.observe _ _ S.bankEq q.source (reduct (thenMap first second.portMap) input)) :=
  Proofs.staged_satisfaction backend input sentence

theorem direct_satisfaction (backend : Backend) (input : Valuation U)
    (sentence : Sentence (Compared first second result)) :
    (sentence.map Compared.direct).Holds (fun q => backend.observe q.artifacts input) ↔
      sentence.Holds (fun q => @Admitted.observe _ _ S.bankEq q.source (reduct (thenMap first second.portMap) input)) :=
  Proofs.direct_satisfaction backend input sentence

theorem satisfaction_iff (backend : Backend) (input : Valuation U)
    (sentence : Sentence (Compared first second result)) :
    (sentence.map Compared.staged).Holds (fun q => backend.observe q.artifacts input) ↔
      (sentence.map Compared.direct).Holds (fun q => backend.observe q.artifacts input) :=
  (staged_satisfaction backend input sentence).trans (direct_satisfaction backend input sentence).symm

end Compared

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition
