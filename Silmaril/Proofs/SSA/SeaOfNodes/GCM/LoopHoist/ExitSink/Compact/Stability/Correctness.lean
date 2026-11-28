module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Rescan
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Identity

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Frame)
open Silmaril.SSA.SeaOfNodes.GCM (EdgeSlot shape)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink (ExitLabel SavedBank TargetCfg)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery (Scan)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Typed (edgePackets)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp)

variable {Input full extra bank kept results : List Width} {saved carried result : Width}
variable {source : TargetCfg Input saved carried result extra full}

theorem rescan (emission : Emission source) :
    ∃ scan, scanExit? (emission.cfg.block .exit) = some scan ∧
      scan.mask = List.replicate (shape.ofBlock (emission.cfg.block .exit)).bindings false ∧
      ∀ index < emission.projection.types.length, index ∈ scan.inputs := by
  obtain ⟨scan, scanned, mask⟩ := scan_kept emission
  obtain ⟨covered, check, complete⟩ := packet_used emission
  have same := Option.some.inj (check.symm.trans scanned)
  exact ⟨scan, scanned, mask, same ▸ complete⟩

private theorem option_heq_some {α β : Type} (same : α = β) {a : Option α} {b : β}
    (compared : HEq a (some b)) : ∃ value, a = some value ∧ HEq value b := by
  subst β
  exact ⟨b, eq_of_heq compared, HEq.rfl⟩

private theorem coverage_heq (same : full = kept)
    {old : Block TargetOp (ExitLabel bank full) (full ++ Input) results}
    {new : Block TargetOp (ExitLabel bank kept) (kept ++ Input) results}
    (equal : HEq old new) : packetUsed? old = packetUsed? new := by
  subst kept
  rw [eq_of_heq equal]

private theorem compact_some {scan : Scan} (scanned : scanExit? (source.block .exit) = some scan)
    {code : Block TargetOp (ExitLabel (SavedBank saved carried extra) (Projection.forReads full scan.inputs).types)
      ((Projection.forReads full scan.inputs).types ++ Input) [result]}
    (rewritten : rewriteExit? scan.mask (Projection.forReads full scan.inputs).rename (source.block .exit) = some code)
    (covered : packetUsed? code = true) :
    compact? source = some ⟨scan, scanned, code, rewritten, covered⟩ := by
  unfold compact?
  split
  · rename_i missing
    rw [scanned] at missing
    contradiction
  · rename_i report found
    have same := Option.some.inj (found.symm.trans scanned)
    subst report
    split
    · rename_i missing
      rw [rewritten] at missing
      contradiction
    · rename_i other checked
      have sameCode := Option.some.inj (checked.symm.trans rewritten)
      subst other
      simp [covered]

theorem compact_again (first : Emission source) :
    ∃ second : Emission first.cfg, compact? first.cfg = some second ∧
      second.projection = Projection.keepAll first.projection.types ∧ HEq second.exitCode first.exitCode := by
  obtain ⟨scan, scanned, mask, complete⟩ := rescan first
  let p := Projection.forReads first.projection.types scan.inputs
  have identity : p = Projection.keepAll first.projection.types :=
    keepAll_of_reads first.projection.types scan.inputs complete
  have types : p.types = first.projection.types := (congrArg Projection.types identity).trans (keepAll_types _)
  have compiles : HEq (rewriteExit? (kept := p.types) scan.mask p.rename (first.cfg.block .exit))
      (some (first.cfg.block .exit)) := by
    rw [identity]
    exact rewrite_keepAll scanned mask
  have sameCodeType :
      Block TargetOp (ExitLabel (SavedBank saved carried extra) p.types) (p.types ++ Input) [result] =
        Block TargetOp (ExitLabel (SavedBank saved carried extra) first.projection.types)
          (first.projection.types ++ Input) [result] :=
    congrArg (fun packet => Block TargetOp (ExitLabel (SavedBank saved carried extra) packet)
      (packet ++ Input) [result]) types
  obtain ⟨code, rewritten, exactCode⟩ := option_heq_some sameCodeType compiles
  have covered := (coverage_heq types exactCode).trans first.covered
  exact ⟨⟨scan, scanned, code, rewritten, covered⟩, compact_some scanned rewritten covered, identity, exactCode⟩

private theorem header_frame_heq (types : kept = full) (packet : Env bank) :
    HEq (⟨.header, packet⟩ : Frame (ExitLabel bank kept)) (⟨.header, packet⟩ : Frame (ExitLabel bank full)) := by
  cases types
  rfl

private theorem exit_frame_heq (types : kept = full) {small : Env kept} {original : Env full}
    (packet : HEq small original) :
    HEq (⟨.exit, small⟩ : Frame (ExitLabel bank kept)) (⟨.exit, original⟩ : Frame (ExitLabel bank full)) := by
  subst kept
  cases packet
  rfl

private theorem frame_keepAll (widths : List Width) (frame : Frame (ExitLabel bank widths)) :
    HEq ((Projection.keepAll widths).frame frame) frame := by
  obtain ⟨label, packet⟩ := frame
  cases label with
  | header => exact header_frame_heq (keepAll_types widths) packet
  | exit => exact exit_frame_heq (keepAll_types widths) (keepAll_values packet)

private theorem packets_map_heq {α β : Type} (types : α = β) (mapFrame : α → β)
    (identity : ∀ frame, HEq (mapFrame frame) frame) (packets : List (EdgeSlot × α)) :
    HEq (packets.map (fun (slot, frame) => (slot, mapFrame frame))) packets := by
  subst β
  have exactMap : mapFrame = id := funext fun frame => eq_of_heq (identity frame)
  subst mapFrame
  have samePair : (fun (slot, frame) => (slot, id frame)) = (id : EdgeSlot × α → EdgeSlot × α) := by
    funext pair
    cases pair
    rfl
  rw [samePair, List.map_id]

theorem same_header_packets (emission : Emission source) (identity : emission.projection = Projection.keepAll full)
    (env : Env (SavedBank saved carried extra ++ Input)) :
    HEq ((emission.cfg.block .header).eval evalOp edgePackets env)
      ((source.block .header).eval evalOp edgePackets env) := by
  apply heq_of_eq_of_heq (header_packets emission env)
  rw [identity]
  exact packets_map_heq (congrArg (fun widths => Frame (ExitLabel (SavedBank saved carried extra) widths))
    (keepAll_types full).symm) (Projection.keepAll full).frame (frame_keepAll full) _

theorem stable (first : Emission source) :
    ∃ second : Emission first.cfg, compact? first.cfg = some second ∧
      second.projection = Projection.keepAll first.projection.types ∧ HEq second.exitCode first.exitCode ∧
      ∀ env : Env (SavedBank saved carried extra ++ Input),
        HEq ((second.cfg.block .header).eval evalOp edgePackets env)
          ((first.cfg.block .header).eval evalOp edgePackets env) := by
  obtain ⟨second, rerun, identity, exactExit⟩ := compact_again first
  exact ⟨second, rerun, identity, exactExit, same_header_packets second identity⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability
