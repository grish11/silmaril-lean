module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Defs

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability

open Silmaril.MLIR.Arith (Var Width)
open Silmaril.MLIR.CF (Block)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.SSA.SeaOfNodes.GCM (shape)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink (ExitLabel TargetCfg)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery (Scan older operandIndices)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp)

variable {Input Γ Δ args full kept bank results extra : List Width}
variable {w saved carried result : Width}
variable {source : TargetCfg Input saved carried result extra full}

private def keepIndex (indexMap : Nat → Option Nat) : Nat → Option Nat
  | 0 => some 0
  | index + 1 => (indexMap index).map Nat.succ

private def dropIndex (indexMap : Nat → Option Nat) : Nat → Option Nat
  | 0 => none
  | index + 1 => indexMap index

private def Indices (rename : PartialRename Γ Δ) (indexMap : Nat → Option Nat) : Prop :=
  ∀ {w} (ref : Var Γ w), (rename ref).map Var.index = indexMap ref.index

private theorem keep_indices {rename : PartialRename Γ Δ} {indexMap : Nat → Option Nat}
    (mapped : Indices rename indexMap) :
    Indices (keepUnder (w := w) rename) (keepIndex indexMap) := by
  intro _ ref
  cases ref with
  | here => rfl
  | there ref =>
    have same := congrArg (fun value : Option Nat => value.map Nat.succ) (mapped ref)
    simpa [keepUnder, Var.index, keepIndex, Option.map_map, Function.comp_def] using same

private theorem drop_indices {rename : PartialRename Γ Δ} {indexMap : Nat → Option Nat}
    (mapped : Indices rename indexMap) :
    Indices (dropUnder (w := w) rename) (dropIndex indexMap) := by
  intro _ ref
  cases ref with
  | here => rfl
  | there ref => exact mapped ref

private theorem operand_indices {rename : PartialRename Γ Δ} {indexMap : Nat → Option Nat}
    (indexed : Indices rename indexMap) {old : Operands Γ args} {new : Operands Δ args}
    (checked : rewriteOperands? rename old = some new) :
    operandIndices new = (operandIndices old).filterMap indexMap := by
  induction old with
  | nil => cases checked; rfl
  | cons ref tail ih =>
    obtain ⟨mapped, selected, rest⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨mappedTail, continued, final⟩ := Option.bind_eq_some_iff.mp rest
    change some (.cons mapped mappedTail) = some new at final
    cases final
    have same := indexed ref
    rw [selected] at same
    change some mapped.index = indexMap ref.index at same
    simp only [operandIndices, List.filterMap_cons, ← same, ih continued]

private theorem older_keep (indexMap : Nat → Option Nat) (reads : List Nat) :
    older (reads.filterMap (keepIndex indexMap)) = (older reads).filterMap indexMap := by
  induction reads with
  | nil => rfl
  | cons index rest ih =>
    cases index with
    | zero => exact ih
    | succ index =>
      cases selected : indexMap index <;>
        simp [older, keepIndex, selected] at ih ⊢ <;> simp_all

private theorem filter_drop (indexMap : Nat → Option Nat) (reads : List Nat) :
    reads.filterMap (dropIndex indexMap) = (older reads).filterMap indexMap := by
  induction reads with
  | nil => rfl
  | cons index rest ih =>
    cases index with
    | zero => exact ih
    | succ index =>
      have split : older ((index + 1) :: rest) = index :: older rest := rfl
      simp only [split, List.filterMap_cons, dropIndex, ih]

private theorem scan_after_rewrite
    {old : Block TargetOp (ExitLabel bank full) Γ results} {new : Block TargetOp (ExitLabel bank kept) Δ results}
    {scan : Scan} (scanned : scanExit? old = some scan) (rename : PartialRename Γ Δ)
    {indexMap : Nat → Option Nat} (indexed : Indices rename indexMap)
    (rewritten : rewriteExit? scan.mask rename old = some new) :
    scanExit? new = some ⟨List.replicate (shape.ofBlock new).bindings false,
      scan.inputs.filterMap indexMap⟩ := by
  induction old generalizing Δ scan indexMap with
  | terminator term =>
    cases term with
    | br => cases scanned
    | condBr => cases scanned
    | ret reads =>
      cases scanned
      obtain ⟨mapped, ready, rfl⟩ := Option.map_eq_some_iff.mp rewritten
      simp [scanExit?, shape.ofBlock, operand_indices indexed ready]
  | letOp op operands tail ih =>
    obtain ⟨report, sourceTail, rfl⟩ := Option.map_eq_some_iff.mp scanned
    by_cases needed : 0 ∈ report.inputs
    · simp only [Scan.beforeBinding, ite_eq_left needed, rewriteExit?] at rewritten
      obtain ⟨mapped, checked, rest⟩ := Option.bind_eq_some_iff.mp rewritten
      obtain ⟨newTail, translated, final⟩ := Option.bind_eq_some_iff.mp rest
      change some (.letOp op mapped newTail) = some new at final
      cases final
      have rescanned := ih sourceTail (keepUnder rename) (keep_indices indexed) translated
      have stays : 0 ∈ report.inputs.filterMap (keepIndex indexMap) :=
        List.mem_filterMap.mpr ⟨0, needed, rfl⟩
      simp only [scanExit?, rescanned, Option.map_some, Scan.beforeBinding, ite_eq_left needed,
        ite_eq_left stays, shape.ofBlock, List.replicate_succ, List.filterMap_append,
        older_keep, operand_indices indexed checked]
    · simp only [Scan.beforeBinding, ite_eq_right needed, rewriteExit?] at rewritten
      simpa only [Scan.beforeBinding, ite_eq_right needed, filter_drop] using
        ih sourceTail (dropUnder rename) (drop_indices indexed) rewritten

private def packetIndex : {widths : List Width} → Projection widths → Nat → Option Nat
  | _, .nil => some
  | _, .keep tail => keepIndex (packetIndex tail)
  | _, .drop tail => dropIndex (packetIndex tail)

private theorem packet_indices (p : Projection full) :
    Indices (p.rename (Input := Input)) (packetIndex p) := by
  induction p with
  | nil => intro _ ref; rfl
  | keep _ ih => exact keep_indices ih
  | drop _ ih => exact drop_indices ih

theorem scan_kept (emission : Emission source) :
    ∃ scan, scanExit? (emission.cfg.block .exit) = some scan ∧
      scan.mask = List.replicate (shape.ofBlock (emission.cfg.block .exit)).bindings false := by
  have scanned := scan_after_rewrite emission.scanned emission.projection.rename
    (packet_indices emission.projection) emission.rewritten
  exact ⟨_, scanned, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability
