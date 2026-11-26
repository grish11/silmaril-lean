module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Native
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Facts
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Compile

/-! The actual compiler preserves observations on the image of a checked port identification. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification

open CategoryTheory Silmaril.Logic.Institution
open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (TupleCovers)
open SeaOfNodes.Loop.SCCP (decideTupleCovers)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open Blocks (Bank)
open SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard (selector selector_run)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution
  (Admitted Backend EntryFacts Sentence SourceReturns admit observationRoom)
open Reindex.Guarded.Institution (AdmittedAt Generated Valuation generatedRoom)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

universe u

variable {S T : EntrySignature} {old new : List (ValueSort Width)} {out : ValueSort Width}
variable {result : Width}

theorem reduct_get (map : PortMap S T) (input : Valuation T) {t : SeaOfNodes.Diamond.Ty Width}
    (port : Port (dataPorts S.regs) t) :
    (reduct map input).get port = input.get (map t port) :=
  Proofs.pull_get map input port

theorem reduct_embedding (embedding : Embedding S T) (input : Valuation T) :
    reduct embedding.portMap input = embedding.reduct input :=
  Proofs.reduct_embedding embedding input

/-- Identified slots agree at every valuation in the image of the reduct. -/
theorem reduct_identifies (map : PortMap S T) (input : Valuation T) {t : SeaOfNodes.Diamond.Ty Width}
    (left right : Port (dataPorts S.regs) t) (identified : map t left = map t right) :
    (reduct map input).get left = (reduct map input).get right := by
  rw [reduct_get, reduct_get, identified]

theorem ports_complete {K : Type u} {ts : List K} {t : K} (port : Port ts t) :
    (⟨t, port⟩ : Sigma (Port ts)) ∈ ports ts :=
  Proofs.ports_complete port

theorem checkWrites_iff (map : BankMap old new) (p : Program Op old out) :
    checkWrites map p = true ↔ SafeWrites map p :=
  Proofs.checkWrites_iff map p

theorem embedding_safe (embedding : Embedding S T) (p : Program Op S.regs out) :
    SafeWrites embedding.portMap p := by
  intro q _ t port shared
  obtain ⟨rfl, same⟩ := Sigma.mk.inj_iff.mp (Reindex.slot_eq _ _ shared)
  exact congrArg slot (embedding.portMap_injective _ (eq_of_heq same))

theorem source_run (map : BankMap old new) (p : Program Op old out)
    (safe : SafeWrites map p) (fuel : Nat) (input : Bank (regs := new) model) :
    (program map p).source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 (pull map input) :=
  Proofs.source_run map p safe fuel input

theorem pushFacts_covers (map : BankMap old new) (facts : EntryFacts old) (combined : EntryFacts new)
    (ok : pushFacts map facts = some combined) (input : Bank (regs := new) model) :
    TupleCovers combined input ↔ TupleCovers facts (pull map input) :=
  Proofs.pushFacts_covers map facts combined ok input

/-- A rejected intersection has no covered entry in the image of the reduct. -/
theorem pushFacts_refuses (map : BankMap old new) (facts : EntryFacts old)
    (refused : pushFacts map facts = none) (input : Bank (regs := new) model) :
    ¬ TupleCovers facts (pull map input) :=
  Proofs.pushFacts_refuses map facts refused input

theorem replay_fact_conflict (map : PortMap S T) (p : AdmittedAt S result)
    (safe : SafeWrites map (@Admitted.source _ _ S.bankEq p))
    (refused : pushFacts map (@Admitted.facts _ _ S.bankEq p) = none) :
    replay map p = .error .incompatibleFacts := by
  simp [replay, (checkWrites_iff _ _).mpr safe, refused]

variable (map : PortMap S T) (p : AdmittedAt S result) {target : Generated T result}
variable (ok : compile map p = .ok target)

include ok

theorem compile_safe : SafeWrites map (@Admitted.source _ _ S.bankEq p) :=
  Proofs.compile_safe map p target ok

/-- The underlying FIFO admission actually ran on the transported quads
and the intersected entry facts. -/
theorem compile_admit :
    @admit _ _ T.bankEq (program map (@Admitted.source _ _ S.bankEq p))
      (@Admitted.facts _ _ T.bankEq target.source) = .ok target.source :=
  Proofs.compile_admit map p target ok

theorem compile_source :
    @Admitted.source _ _ T.bankEq target.source = program map (@Admitted.source _ _ S.bankEq p) :=
  Proofs.compile_source map p target ok

theorem compile_coverage (input : Valuation T) :
    TupleCovers (@Admitted.facts _ _ T.bankEq target.source) input ↔
      TupleCovers (@Admitted.facts _ _ S.bankEq p) (reduct map input) :=
  Proofs.compile_coverage map p target ok input

/-- The actual numbered selectors for the two guarded emissions choose the same arm. -/
theorem numbered_guard (input : Valuation T) :
    (selector (@Admitted.facts _ _ T.bankEq target.source)).2.toGraph.run (Join.model model) input =
      (selector (@Admitted.facts _ _ S.bankEq p)).2.toGraph.run (Join.model model) (reduct map input) := by
  have tag :
      @decide _ (@decideTupleCovers _ _ _ T.bankEq (@Admitted.facts _ _ T.bankEq target.source) input) =
      @decide _ (@decideTupleCovers _ _ _ S.bankEq (@Admitted.facts _ _ S.bankEq p) (reduct map input)) :=
    decide_eq_decide.mpr (compile_coverage map p ok input)
  refine (@selector_run _ T.bankEq _ input).trans ?_
  rw [tag]
  exact (@selector_run _ S.bankEq _ (reduct map input)).symm

theorem compile_native_run (fuel : Nat) (input : Valuation T) :
    (@Admitted.source _ _ T.bankEq target.source).source.runFrom model fuel 0 input =
      (@Admitted.source _ _ S.bankEq p).source.runFrom model fuel 0 (reduct map input) := by
  rw [compile_source map p ok]
  exact source_run map _ (compile_safe map p ok) fuel input

/-- Each backend has its own finite witness. The original run is at the
pullback valuation, for covered and fallback inputs alike. -/
theorem compile_returns_iff (backend : Backend) (input : Valuation T) (word : Word result) :
    backend.Returns target.artifacts input word ↔
      SourceReturns (@Admitted.source _ _ S.bankEq p) (reduct map input) word := by
  have adequacy := @Backend.returns_iff_source _ _ T.bankEq backend target.source input word
  rw [← target.generated] at adequacy
  exact adequacy.trans (exists_congr fun fuel => Iff.of_eq
    (congrArg (fun ran => ran = some word) (compile_native_run map p ok fuel input)))

theorem compile_noReturn_iff (backend : Backend) (input : Valuation T) :
    (¬ ∃ word, backend.Returns target.artifacts input word) ↔
      ¬ ∃ word, SourceReturns (@Admitted.source _ _ S.bankEq p) (reduct map input) word :=
  not_congr (exists_congr (compile_returns_iff map p ok backend input))

theorem compile_observe (backend : Backend) (input : Valuation T) :
    backend.observe target.artifacts input = @Admitted.observe _ _ S.bankEq p (reduct map input) :=
  Part.ext fun word => (backend.mem_observe_iff ..).trans
    ((compile_returns_iff map p ok backend input word).trans
      (@Admitted.mem_observe_iff _ _ S.bankEq _ _ _).symm)

omit ok

theorem satisfaction (backend : Backend) (input : Valuation T) (sentence : Sentence (Compiled map result)) :
    (sentence.map Compiled.target).Holds (fun q => backend.observe q.artifacts input) ↔
      sentence.Holds (fun q => @Admitted.observe _ _ S.bankEq q.source (reduct map input)) := by
  cases sentence <;> simp only [Sentence.map, Sentence.Holds,
    fun q : Compiled map result => compile_observe map q.source q.success backend input]

/-- Only programs that passed contraction and replay enter this local source room. -/
@[expose] noncomputable def checkedSourceRoom (result : Width) : Room.{0, 0, 0} :=
  observationRoom (fun (q : Compiled map result) => @Admitted.observe _ _ S.bankEq q.source)

/-- The model leg is the typed pullback; the sentence leg uses actual emitted artifacts. -/
@[expose] noncomputable def corridor (result : Width) (backend : Backend) :
    checkedSourceRoom map result ⟶ generatedRoom result backend T :=
  ⟨Sentence.map Compiled.target, Discrete.functor (fun input : Valuation T => Discrete.mk (reduct map input)),
    fun input sentence => satisfaction map backend input.as sentence⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification
