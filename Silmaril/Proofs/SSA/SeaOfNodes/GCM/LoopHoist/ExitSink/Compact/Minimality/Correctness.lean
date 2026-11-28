module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality

open Silmaril.MLIR.Arith (Var Width)
open Silmaril.MLIR.CF (Block)
open Silmaril.MLIR.Pure (Code Operands)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink (ExitLabel TargetCfg)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery (Scan older operandIndices)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp)

variable {Input Γ Δ args full kept bank results extra : List Width}
variable {w saved carried result : Width}

private theorem bind_isSome {α β : Type} {first : Option α} {next : α → Option β}
    {goal : Prop} (succeeds : ∀ a, (next a).isSome = true ↔ goal) :
    (first.bind next).isSome = true ↔ first.isSome = true ∧ goal := by
  cases first <;> simp [succeeds]

private theorem bind_pure_isSome {α β : Type} (first : Option α) (make : α → β) :
    (first.bind fun a => some (make a)).isSome = first.isSome := by
  cases first <;> rfl

private theorem operands_iff {rename : PartialRename Γ Δ} {available : Nat → Prop}
    (resolves : ∀ {w} (ref : Var Γ w), (rename ref).isSome = true ↔ available ref.index)
    (operands : Operands Γ args) :
    (rewriteOperands? rename operands).isSome = true ↔ ∀ i ∈ operandIndices operands, available i := by
  induction operands with
  | nil => simp [rewriteOperands?, operandIndices]
  | cons ref rest ih =>
    change ((rename ref).bind fun mapped =>
      (rewriteOperands? rename rest).bind fun tail => some (Operands.cons mapped tail)).isSome = true ↔ _
    rw [bind_isSome (fun _ => by simpa only [bind_pure_isSome] using ih), resolves]
    simp [operandIndices]

private def underIndex (here : Prop) (available : Nat → Prop) : Nat → Prop
  | 0 => here
  | i + 1 => available i

private theorem kept_index {argsWidth : Width} {rename : PartialRename Γ Δ} {available : Nat → Prop}
    (resolves : ∀ {w} (ref : Var Γ w), (rename ref).isSome = true ↔ available ref.index)
    (ref : Var (w :: Γ) argsWidth) :
    ((keepUnder rename) ref).isSome = true ↔ underIndex True available ref.index := by
  cases ref <;> simp [keepUnder, Var.index, underIndex, resolves]

private theorem dropped_index {argsWidth : Width} {rename : PartialRename Γ Δ} {available : Nat → Prop}
    (resolves : ∀ {w} (ref : Var Γ w), (rename ref).isSome = true ↔ available ref.index)
    (ref : Var (w :: Γ) argsWidth) :
    ((dropUnder rename) ref).isSome = true ↔ underIndex False available ref.index := by
  cases ref <;> simp [dropUnder, Var.index, underIndex, resolves]

private theorem demand_under (here : Prop) (available : Nat → Prop) (reads : List Nat) :
    (∀ i ∈ reads, underIndex here available i) ↔
      (0 ∈ reads → here) ∧ ∀ i ∈ older reads, available i := by
  constructor
  · intro used
    refine ⟨fun root => used 0 root, ?_⟩
    intro index present
    obtain ⟨newer, original, shifted⟩ := List.mem_filterMap.mp present
    cases newer with
    | zero => cases shifted
    | succ newer =>
      change some newer = some index at shifted
      cases shifted
      exact used (index + 1) original
  · rintro ⟨root, tail⟩ index needed
    cases index with
    | zero => exact root needed
    | succ index => exact tail index (List.mem_filterMap.mpr ⟨index + 1, needed, rfl⟩)

private theorem rewrite_iff {code : Block TargetOp (ExitLabel bank full) Γ results} {scan : Scan}
    (scanned : scanExit? code = some scan) (rename : PartialRename Γ Δ) {available : Nat → Prop}
    (resolves : ∀ {w} (ref : Var Γ w), (rename ref).isSome = true ↔ available ref.index) :
    (rewriteExit? (kept := kept) scan.mask rename code).isSome = true ↔
      ∀ i ∈ scan.inputs, available i := by
  induction code generalizing Δ scan available with
  | terminator term =>
    cases term with
    | br => cases scanned
    | condBr => cases scanned
    | ret values =>
      cases scanned
      simpa [rewriteExit?] using operands_iff resolves values
  | letOp op operands tail ih =>
    obtain ⟨tailScan, scannedTail, rfl⟩ := Option.map_eq_some_iff.mp scanned
    by_cases needed : 0 ∈ tailScan.inputs
    · simp only [Scan.beforeBinding, ite_eq_left needed, rewriteExit?]
      change ((rewriteOperands? rename operands).bind fun mapped =>
        (rewriteExit? (kept := kept) tailScan.mask (keepUnder rename) tail).bind fun code =>
          some (Code.letOp op mapped code)).isSome = true ↔ _
      have tailIff := ih scannedTail (keepUnder rename) (available := underIndex True available) (kept_index resolves)
      rw [bind_isSome (fun _ => by simpa only [bind_pure_isSome] using tailIff), operands_iff resolves,
        demand_under, List.forall_mem_append]
      simp only [implies_true, true_and]
      exact and_comm
    · simp only [Scan.beforeBinding, ite_eq_right needed, rewriteExit?]
      rw [ih scannedTail (dropUnder rename) (available := underIndex False available) (dropped_index resolves), demand_under]
      simp [needed]

private theorem projection_ref (p : Projection full) (ref : Var (full ++ Input) w) :
    (p.rename ref).isSome = true ↔ (ref.index < full.length → ref.index ∈ p.indices) := by
  induction p with
  | nil => simp [Projection.rename]; rfl
  | @keep width _ p ih =>
    cases ref with
    | here => simp [Projection.rename, Projection.indices, keepUnder, Var.index]; rfl
    | there ref =>
      simp [Projection.rename, Projection.indices, keepUnder, Var.index, List.mem_map]
      change ((p.rename (Input := Input) ref).map (Var.there (v := width))).isSome = true ↔ _
      rw [Option.isSome_map]
      exact ih ref
  | drop p ih =>
    cases ref with
    | here => simp [Projection.rename, Projection.indices, dropUnder, Var.index, List.mem_map]; rfl
    | there ref =>
      simp [Projection.rename, Projection.indices, dropUnder, Var.index, List.mem_map]
      exact ih ref

theorem projection_rewrite_iff (p : Projection full)
    {code : Block TargetOp (ExitLabel bank full) (full ++ Input) results} {scan : Scan}
    (scanned : scanExit? code = some scan) :
    (p.rewriteScanned? code).isSome = true ↔
      ∀ index ∈ scan.inputs, index < full.length → index ∈ p.indices := by
  simp only [Projection.rewriteScanned?, scanned]
  exact rewrite_iff scanned p.rename (projection_ref p)

theorem minimal {source : TargetCfg Input saved carried result extra full} (emission : Emission source) (p : Projection full) :
    (p.rewriteScanned? (source.block .exit)).isSome = true ↔
      ∀ index ∈ emission.projection.indices, index ∈ p.indices := by
  rw [projection_rewrite_iff p emission.scanned]
  constructor
  · intro admitted index kept
    obtain ⟨inBounds, needed⟩ := (packet_indices emission index).mp kept
    exact admitted index needed inBounds
  · intro retained index needed inBounds
    exact retained index ((packet_indices emission index).mpr ⟨inBounds, needed⟩)

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality
