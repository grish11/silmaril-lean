module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Thms

import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Composition

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame packValues)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF (i64)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)
open Silmaril.SSA.SeaOfNodes.MLIR (sourceInputs)
open Silmaril.SSA.PhiView (latch)

variable {old new tests : Nat} {rtlEntry rtlHeader : List (List PortTy)}
variable {entrySigs sigs : List (List (Diamond.Ty Width))}
variable {mapping : InputMap old new} {source : Family.Source old old rtlEntry rtlHeader tests}
variable {g : Program new old entrySigs sigs} {wires : Live new old sigs}

/-- The actual RTL producer frame establishes the typed snapshot from local header agreement. -/
theorem predecessor_snapshot (sys : Setup mapping source g wires) (input : WordTuple new)
    {carried next : WordTuple old} {before ready after : Frame Reg} {mem : Memory}
    {slot : Fin (tests + 1)} {block : Block Reg}
    (alignment : HeaderMatch sys input carried)
    (cut : FeedbackCut (mapCaptures mapping source) sys.rtl input carried before ready after mem slot next block) :
    Snapshot (scope := liveRegs wires) (List.length_map ..)
      ((livePacket g wires input carried).append (wordEnv input)) ready :=
  Proofs.predecessor_snapshot sys input alignment cut

/-- A continuing visit executes both real targets and latches the exact explicit-Φ bank. -/
theorem visit_correct (sys : Setup mapping source g wires) (input : WordTuple new) (mem : Memory)
    {carried next : WordTuple old} {slot : Fin (tests + 1)} (before : Frame Reg)
    (matched : ArgsMatch before (appendTuple carried input)) (aligned : HeaderMatch sys input carried)
    (taken : source.step (mapping.pull input) carried = .inr (slot, next)) :
    ∃ after, Visit sys input mem slot carried next before after :=
  Proofs.visit_correct sys input mem before matched aligned taken

/-- Compose the per-visit invariant through any admitted finite feedback prefix. -/
theorem prefix_correct (sys : Setup mapping source g wires) (input : WordTuple new) (mem : Memory)
    {slots : List (Fin (tests + 1))} {carried finish : WordTuple old}
    (admitted : Admitted sys input slots carried finish) (before : Frame Reg)
    (matched : ArgsMatch before (appendTuple carried input)) :
    ∃ after, Realized sys input mem slots carried before finish after :=
  Proofs.prefix_correct sys input mem admitted before matched

/-- Consume each backend's exact prefix cost, leaving its independent continuation budget at the final header. -/
theorem realized_run (sys : Setup mapping source g wires) (input : WordTuple new) (mem : Memory)
    {slots : List (Fin (tests + 1))} {carried finish : WordTuple old} {before after : Frame Reg}
    (path : Realized sys input mem slots carried before finish after) (rtlBudget cfBudget : Nat) :
    run sys.rtl (rtlCost rtlHeader.length slots + rtlBudget) ⟨⟨0, 1, 0⟩, before, [], mem⟩ =
      run sys.rtl rtlBudget ⟨⟨0, 1, 0⟩, after, [], mem⟩ ∧
    sys.cf.runFrom evalOp (cfCost slots + cfBudget) (wordEnv input) (headerFrame _ _ carried) =
      sys.cf.runFrom evalOp cfBudget (wordEnv input) (headerFrame _ _ finish) ∧
    ArgsMatch after (appendTuple finish input) :=
  Proofs.realized_run sys input mem path rtlBudget cfBudget

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix
