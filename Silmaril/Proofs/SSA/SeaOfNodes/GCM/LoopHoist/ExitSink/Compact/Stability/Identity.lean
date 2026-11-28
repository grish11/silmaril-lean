module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Defs

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.SSA.SeaOfNodes.GCM (shape)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink (ExitLabel)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery (Scan)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp)

variable {Input Γ Δ args full kept bank results : List Width} {w v : Width}

theorem keepAll_types (widths : List Width) : (Projection.keepAll widths).types = widths := by
  induction widths with
  | nil => rfl
  | cons _ rest ih => simp [Projection.keepAll, Projection.types, ih]

theorem keepAll_indices (widths : List Width) : (Projection.keepAll widths).indices = List.range widths.length := by
  induction widths with
  | nil => rfl
  | cons _ rest ih =>
    simp only [Projection.keepAll, Projection.indices, List.length_cons, List.range_succ_eq_map, ih]

private theorem keepAll_ofPredicate (widths : List Width) (wanted : Nat → Bool)
    (covered : ∀ index < widths.length, wanted index = true) :
    Projection.ofPredicate widths wanted = Projection.keepAll widths := by
  induction widths generalizing wanted with
  | nil => rfl
  | cons _ rest ih =>
    have first := covered 0 (by simp)
    have tail := ih (fun index => wanted index.succ) (fun index bound => covered index.succ (by simpa using bound))
    simp [Projection.ofPredicate, Projection.keepAll, first, tail]

theorem keepAll_of_reads (widths : List Width) (reads : List Nat)
    (covered : ∀ index < widths.length, index ∈ reads) :
    Projection.forReads widths reads = Projection.keepAll widths :=
  keepAll_ofPredicate widths reads.contains (fun index bound => by simpa using covered index bound)

private theorem cons_heq {left : Env Γ} {right : Env Δ} (same : Γ = Δ) (value : BitVec w.val)
    (agree : HEq left right) : HEq (Env.cons value left) (Env.cons value right) := by
  cases same
  cases agree
  rfl

theorem keepAll_values (packet : Env full) : HEq ((Projection.keepAll full).values packet) packet := by
  induction packet with
  | nil => rfl
  | cons value rest ih => exact cons_heq (keepAll_types _) value ih

private theorem here_heq (same : Γ = Δ) :
    HEq (some (@Var.here Γ w)) (some (@Var.here Δ w)) := by
  cases same
  rfl

private theorem there_heq (same : Γ = Δ) {mapped : Option (Var Γ w)} {ref : Var Δ w}
    (agree : HEq mapped (some ref)) :
    HEq (mapped.map (Var.there (v := v))) (some (Var.there (v := v) ref)) := by
  cases same
  cases agree
  rfl

private theorem keepAll_rename (ref : Var (full ++ Input) w) :
    HEq ((Projection.keepAll full).rename (Input := Input) ref) (some ref) := by
  induction full with
  | nil => rfl
  | cons width rest ih =>
    cases ref with
    | here => exact here_heq (congrArg (· ++ Input) (keepAll_types rest))
    | there ref => exact there_heq (congrArg (· ++ Input) (keepAll_types rest)) (ih ref)

private theorem operands_identity (operands : Operands Γ args) :
    rewriteOperands? (fun {_} ref => some ref) operands = some operands := by
  induction operands with
  | nil => rfl
  | cons ref rest ih => simp [rewriteOperands?, ih]

private theorem rewrite_all_kept {code : Block TargetOp (ExitLabel bank full) Γ results}
    {scan : Scan} (scanned : scanExit? code = some scan) :
    rewriteExit? (kept := full) (List.replicate (shape.ofBlock code).bindings false)
      (fun {_} ref => some ref) code = some code := by
  induction code generalizing scan with
  | terminator term =>
    cases term with
    | br => cases scanned
    | condBr => cases scanned
    | ret operands => simp [shape.ofBlock, rewriteExit?, operands_identity]
  | @letOp scope ins width op operands tail ih =>
    obtain ⟨tailScan, scanTail, _⟩ := Option.map_eq_some_iff.mp scanned
    have identity :
        (keepUnder (w := width) (fun {_} (ref : Var scope _) => some ref) :
          PartialRename (width :: scope) (width :: scope)) =
        (fun {_} ref => some ref) := by
      funext valueType ref
      cases ref <;> rfl
    simp [shape.ofBlock, List.replicate_succ, rewriteExit?, operands_identity, identity, ih scanTail]

private theorem rewrite_of_identity {code : Block TargetOp (ExitLabel bank full) Γ results}
    {scan : Scan} (scanned : scanExit? code = some scan)
    (mask : scan.mask = List.replicate (shape.ofBlock code).bindings false)
    (sameScope : Δ = Γ) (samePacket : kept = full) (rename : PartialRename Γ Δ)
    (agree : ∀ {w} (ref : Var Γ w), HEq (rename ref) (some ref)) :
    HEq (rewriteExit? (kept := kept) scan.mask rename code) (some code) := by
  subst Δ
  subst kept
  have sameRename : @rename = ((fun {_} ref => some ref) : PartialRename Γ Γ) := by
    funext valueType ref
    exact eq_of_heq (agree ref)
  rw [mask, sameRename, rewrite_all_kept scanned]

theorem rewrite_keepAll {code : Block TargetOp (ExitLabel bank full) (full ++ Input) results}
    {scan : Scan} (scanned : scanExit? code = some scan)
    (mask : scan.mask = List.replicate (shape.ofBlock code).bindings false) :
    HEq (rewriteExit? (kept := (Projection.keepAll full).types) scan.mask
      ((Projection.keepAll full).rename (Input := Input)) code) (some code) :=
  rewrite_of_identity scanned mask (congrArg (· ++ Input) (keepAll_types full)) (keepAll_types full)
    (Projection.keepAll full).rename keepAll_rename

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability
