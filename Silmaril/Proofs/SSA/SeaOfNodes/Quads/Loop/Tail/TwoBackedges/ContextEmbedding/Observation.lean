module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded.Thms

/-! Iterate the original semantic and checker transport laws along a factored embedding. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Proofs

open SeaOfNodes.Diamond.SCCP (TupleCovers)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted Backend)
open Reindex.Guarded.Institution (AdmittedAt Generated Valuation)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T : EntrySignature} {result : Width}

theorem selectedSide_map (path : Embedding S T) (p : AdmittedAt S result) :
    selectedSide (path.mapAdmitted p) = selectedSide p := by
  induction path with
  | id _ => rfl
  | permute order rest ih => exact ih _
  | weaken fresh rest ih => exact (ih _).trans (Weakening.Guarded.selected_side fresh p)

theorem coverage_iff (path : Embedding S T) (p : AdmittedAt S result) (input : Valuation T) :
    TupleCovers (@Admitted.facts _ _ T.bankEq (path.mapAdmitted p)) input ↔
      TupleCovers (@Admitted.facts _ _ S.bankEq p) (path.reduct input) := by
  induction path with
  | id _ => rfl
  | @permute source middle target order rest ih =>
    exact (ih _ input).trans (Reindex.covers_iff order (@Admitted.facts _ _ source.bankEq p) (rest.reduct input))
  | @weaken source target fresh rest ih =>
    exact (ih _ input).trans (Weakening.covers_iff (@Admitted.facts _ _ source.bankEq p) (rest.reduct input))

theorem native_observe (path : Embedding S T) (p : AdmittedAt S result) (input : Valuation T) :
    @Admitted.observe _ _ T.bankEq (path.mapAdmitted p) input =
      @Admitted.observe _ _ S.bankEq p (path.reduct input) := by
  induction path with
  | id _ => rfl
  | permute order rest ih =>
    exact (ih _ input).trans (Reindex.Guarded.Institution.native_observe_map order p (rest.reduct input))
  | weaken fresh rest ih =>
    exact (ih _ input).trans (Weakening.Guarded.native_observe fresh p (rest.reduct input))

theorem backend_returns (path : Embedding S T) (backend : Backend) (p : Generated S result)
    (input : Valuation T) (word : Word result) :
    backend.Returns (path.mapGenerated p).artifacts input word ↔
      backend.Returns p.artifacts (path.reduct input) word := by
  induction path with
  | id _ => rfl
  | permute order rest ih =>
    exact (ih _ input).trans (p.returns_map backend order (rest.reduct input) word)
  | weaken fresh rest ih =>
    exact (ih _ input).trans (Weakening.Guarded.backend_returns fresh backend p (rest.reduct input) word)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Proofs
