module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame)
open AfterReorder.Second (savedHeader)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input extra : List Width} {saved carried result : Width}
variable {state : Layout.State Input saved carried result extra} {request : Nomination} {move : Move state}

/-- A successful splice is adjacent and legal in the input CFG. A scan of the
    rewritten header recovers the same operand sites and exact use occurrences. -/
theorem emit?_spec (accepted : emit? state request = some move) :
    move.request = request ∧ CrossBlock.keep? state request.origin = some move.binding ∧
    (move.insertion + 1 = move.binding.index ∨ move.binding.index + 1 = move.insertion) ∧
    Legal state.cfg move.binding.sites.operands move.binding.sites.uses move.cut ∧
    Header.Typed.swapAt? (min move.binding.index move.insertion) (state.cfg.block .header) = some move.header ∧
    CrossBlock.findSites? move.next move.insertion 0 (Saved.origins (extra ++ [saved]))
      (move.next.cfg.block .header) = some move.binding.sites :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.emit?_spec accepted

/-- Only the two adjacent typed operations change positions. -/
theorem emit?_order (accepted : emit? state request = some move) :
    ∃ (prefixOps : List Header.Earlier.Operation) (left right : Header.Earlier.Operation)
      (suffixOps : List Header.Earlier.Operation),
      prefixOps.length = min move.binding.index move.insertion ∧
      Header.Earlier.operations (state.cfg.block .header) = prefixOps ++ (left :: right :: suffixOps) ∧
      Header.Earlier.operations (move.next.cfg.block .header) = prefixOps ++ (right :: left :: suffixOps) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.emit?_order accepted

/-- A known live binding cannot be emitted at an illegal original cut. -/
theorem emit?_refuses {binding : CrossBlock.Kept (Label saved carried result extra)}
    (found : CrossBlock.keep? state request.origin = some binding)
    (illegal : ¬ Legal state.cfg binding.sites.operands binding.sites.uses ⟨savedHeader, request.cut⟩) :
    emit? state request = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.emit?_refuses found illegal

/-- The new header is shared with the append reference. The physical prefix,
    slot map and entry invariant still agree. -/
theorem next_invariant (valid : Layout.Invariant state) : Layout.Invariant move.next :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.next_invariant valid

/-- The entry and exit blocks stay identical. Every typed frame yields the
    same branch decision and exact successor frame or return. -/
theorem emit?_frames (accepted : emit? state request = some move) (input : Env Input) :
    move.next.cfg.entry = state.cfg.entry ∧
    move.next.cfg.block .exit = state.cfg.block .exit ∧
    ∀ frame : Frame (Label saved carried result extra),
      (move.next.cfg.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        (state.cfg.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.emit?_frames accepted input

/-- Evaluate the argument tuple of each branch occurrence independently of
    the selected edge, in its original slot order. -/
theorem emit?_edgePackets (accepted : emit? state request = some move)
    (env : Env (((extra ++ [saved]) ++ [carried]) ++ Input)) :
    (move.next.cfg.block .header).eval evalOp Header.Typed.edgePackets env =
      (state.cfg.block .header).eval evalOp Header.Typed.edgePackets env :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.emit?_edgePackets accepted env

/-- The checked splice transports the existing saved-packet routing invariant. -/
theorem emit?_routes {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {input : Env Input} {values : Env (extra ++ [saved])}
    (accepted : emit? state request = some move) (prior : RoutesWith base state.cfg input values) :
    RoutesWith base move.next.cfg input values :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.emit?_routes accepted prior

/-- Each block visit is preserved, so returns and exhaustion use common fuel. -/
theorem emit?_run_eq (accepted : emit? state request = some move) (input : Env Input) (fuel : Nat) :
    move.next.cfg.run evalOp fuel input = state.cfg.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.emit?_run_eq accepted input fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
/-- Partial denotation agrees on return values and their domain. -/
theorem emit?_denotePart (accepted : emit? state request = some move) (input : Env Input) :
    (Cfg.embed move.next.cfg).denotePart evalOp input = (Cfg.embed state.cfg).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.emit?_denotePart accepted input

variable {ranked : Ranked state} {headerCut : Nat}

/-- Ranking consumes the existing cross-block analysis and the actual header splice. -/
theorem rank?_spec (accepted : rank? state request headerCut = some ranked) :
    CrossBlock.analyze? state request = some ranked.crossBlock ∧
    ranked.header = emit? state ⟨request.origin, headerCut⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.rank?_spec accepted

/-- Adding an emitted header candidate preserves the certified depth decision. -/
theorem selection_depth (ranked : Ranked state) :
    ranked.crossBlock.control.depth ranked.selection.1.block =
      ranked.crossBlock.control.depth ranked.crossBlock.point.block :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.selection_depth ranked

/-- The selected block has minimum depth across both header cuts and the admitted preheader. -/
theorem selected_minDepth (ranked : Ranked state) :
    ranked.crossBlock.control.depth ranked.selection.1.block ≤ ranked.crossBlock.control.depth savedHeader ∧
    (ranked.crossBlock.preheader.isSome →
      ranked.crossBlock.control.depth ranked.selection.1.block ≤ ranked.crossBlock.control.depth none) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.selected_minDepth ranked

/-- A later checked header cut wins exactly when the depth decision stays in the header. -/
theorem laterHeader?_iff (move : Move state) :
    ranked.laterHeader? = some move ↔
      ranked.crossBlock.selectedMove?.isSome = false ∧ ranked.header = some move ∧
        ranked.crossBlock.kept.point.cut < move.cut.cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.laterHeader?_iff move

/-- The emitted header candidate resolves the same binding and sites as the existing ranker. -/
theorem rank?_candidate (accepted : rank? state request headerCut = some ranked)
    (candidate : ranked.header = some move) :
    emit? state ⟨request.origin, headerCut⟩ = some move ∧ move.binding = ranked.crossBlock.kept :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.rank?_candidate accepted candidate

/-- The selected typed CFG preserves observations at every common block fuel. -/
theorem rank?_run_eq {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    (accepted : rank? state request headerCut = some ranked) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : RoutesWith base state.cfg input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) (fuel : Nat) :
    ranked.selection.2.2.cfg.run evalOp fuel input = state.cfg.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.rank?_run_eq accepted valid prior matched fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
/-- The selected typed CFG preserves partial denotation. -/
theorem rank?_denotePart {base : Silmaril.MLIR.CF.Cfg TargetOp (SourceLabel carried result) Input [result]}
    (accepted : rank? state request headerCut = some ranked) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : RoutesWith base state.cfg input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) :
    (Cfg.embed ranked.selection.2.2.cfg).denotePart evalOp input = (Cfg.embed state.cfg).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.rank?_denotePart accepted valid prior matched

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice
