module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Ports.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Correctness

/-! Exact typed factorization and observations of the independently checked guarded routes. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (TupleCovers)
open SeaOfNodes.Loop.MLIR.CF (Op)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open Identification (PortMap reduct checkWrites)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted Backend Sentence SourceReturns)
open Reindex.Guarded.Institution (Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T : EntrySignature} {result : Width} {t : SeaOfNodes.Diamond.Ty Width}

theorem thenMap_eq (map : PortMap S T) : Composition.thenMap (compress map) (embedding map).portMap = map :=
  Proofs.thenMap_eq map

theorem compress_surjective (map : PortMap S T) (sort : SeaOfNodes.Diamond.Ty Width) :
    Function.Surjective (compress map sort) :=
  Proofs.compress_surjective map sort

theorem embedding_image (map : PortMap S T) (target : Port (dataPorts T.regs) t) :
    (∃ kept, (embedding map).portMap t kept = target) ↔ ∃ old, map t old = target :=
  Proofs.embedding_image map target

theorem reduct_factor (map : PortMap S T) (input : Valuation T) :
    reduct map input = reduct (compress map) ((embedding map).reduct input) :=
  (congrArg (fun m => reduct m input) (thenMap_eq map).symm).trans
    (Composition.reduct_embedding (compress map) (embedding map) input)

/-- The compressed and final maps identify exactly the same old destinations and aliases. -/
theorem checkWrites_compress (map : PortMap S T) {out : ValueSort Width} (p : Program Op S.regs out) :
    checkWrites (compress map) p = checkWrites map p := by
  simpa only [thenMap_eq map] using (Composition.checkWrites_embedding (compress map) (embedding map) p).symm

variable {map : PortMap S T}

theorem staged_compiled (q : Compared map result) : compileStaged map q.source = .ok q.staged :=
  q.staged_compiled

/-- The direct artifact in the comparison is an actual successful compilation of the supplied map. -/
theorem direct_compiled (q : Compared map result) : Identification.compile map q.source = .ok q.direct := by
  simpa only [thenMap_eq map] using q.composed

variable {input : Valuation S} {fill target : Valuation T}

/-- The actual staged contract covers a lift precisely when the old contract covers the input. -/
theorem staged_coverage_at_lift (q : Compared map result) (lifted : liftChecked map input fill = some target) :
    TupleCovers (@Admitted.facts _ _ T.bankEq q.staged.source) target ↔
      TupleCovers (@Admitted.facts _ _ S.bankEq q.source) input := by
  simpa only [thenMap_eq map, liftChecked_sound map input fill target lifted] using q.staged_coverage target

/-- Each backend uses its own finite return witness. The old input is precisely the lifted valuation's reduct. -/
theorem staged_returns_at_lift (q : Compared map result) (lifted : liftChecked map input fill = some target)
    (backend : Backend) (word : Word result) :
    backend.Returns q.staged.artifacts target word ↔
      SourceReturns (@Admitted.source _ _ S.bankEq q.source) input word := by
  simpa only [thenMap_eq map, liftChecked_sound map input fill target lifted] using q.staged_returns backend target word

theorem staged_satisfaction_at_lift (lifted : liftChecked map input fill = some target)
    (backend : Backend) (sentence : Sentence (Compared map result)) :
    (sentence.map Composition.Compared.staged).Holds (fun q => backend.observe q.artifacts target) ↔
      sentence.Holds (fun q => @Admitted.observe _ _ S.bankEq q.source input) := by
  simpa only [thenMap_eq map, liftChecked_sound map input fill target lifted] using
    Composition.Compared.staged_satisfaction backend target sentence

theorem direct_satisfaction_at_lift (lifted : liftChecked map input fill = some target)
    (backend : Backend) (sentence : Sentence (Compared map result)) :
    (sentence.map Composition.Compared.direct).Holds (fun q => backend.observe q.artifacts target) ↔
      sentence.Holds (fun q => @Admitted.observe _ _ S.bankEq q.source input) := by
  simpa only [thenMap_eq map, liftChecked_sound map input fill target lifted] using
    Composition.Compared.direct_satisfaction backend target sentence

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization
