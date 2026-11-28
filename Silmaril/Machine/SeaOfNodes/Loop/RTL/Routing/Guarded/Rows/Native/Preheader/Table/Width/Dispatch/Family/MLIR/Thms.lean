module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Correctness

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg PortTy)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF (i64)
open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.MLIR (sourceInputs)
open Silmaril.SSA.SeaOfNodes.MLIR.Lowering (Scope)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)
open Silmaril.SSA.RVSDG (Tuple Locals Origin extend)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)

variable {scope : List Reg} {bank tests captures live : Nat} {fn : Func Reg}

/-- A checked row reconstructs the original machine block at its positional occurrence. -/
theorem row_roundTrip (plan : Plan fn scope bank tests) (slot : Fin (tests + 1)) :
    fn.block? (occurrence slot).1 = some ⟨[], [], (plan.row slot).term⟩ :=
  Proofs.row_roundTrip plan slot

/-- The CF projection and the existing explicit-Φ view decode the same RTL occurrence. -/
theorem column_eq_phi (plan : Plan fn scope bank tests) (view : Phi.Checked fn tests)
    (slot : Fin (tests + 1)) :
    view.reemit slot.succ = some (1, (plan.row slot).column.registers) :=
  Proofs.column_eq_phi plan view slot

/-- The checked projection reads exactly the ordered RTL operand list from the old frame. -/
theorem column_reads {Γ : List Width} {n : Nat} (width : scope.length = live)
    (env : Env (wordsTy live ++ Γ)) (frame : Frame Reg)
    (matched : Snapshot width env frame) (column : Phi.Packet scope n) :
    frame.readAll column.registers =
      some (wordList ((project (fun i => argAt live (i.cast width)) column).eval env)) :=
  Proofs.column_reads width env frame matched column

/-- The header edge packs the selected typed origins in the declared order. -/
theorem liveOperands_eval {args : List (Diamond.Ty Width)} {past : List (List (Diamond.Ty Width))}
    {Δ : List Width} {names : Scope args past Δ} {env : Env Δ}
    {values : Tuple (Diamond.Val Silmaril.SSA.SeaOfNodes.MLIR.Word) args}
    {locals : Locals (Diamond.Val Silmaril.SSA.SeaOfNodes.MLIR.Word) past} (agree : names.Agrees env values locals)
    (wires : List (Origin args past (.value (.data i64)))) :
    (liveOperands names wires).eval env = readLive values locals wires :=
  Proofs.liveOperands_eval agree wires

variable {entrySigs sigs : List (List (Diamond.Ty Width))}

/-- The actual header code executes the producer table and passes its live words to the first dispatcher. -/
theorem header_frame (g : Program captures bank entrySigs sigs) (wires : Live captures bank sigs)
    (plan : Plan fn (liveRegs wires) bank tests)
    (input : Env (wordsTy captures)) (old : Loop.MLIR.CF.Bank.Values (wordsTy bank)) :
    let args := appendTuple old (sourceInputs input)
    let locals := g.header.eval Loop.MLIR.CF.model args PUnit.unit
    ((lower g wires plan).block .header).eval evalOp (fun term env => term.eval env)
      ((Loop.MLIR.CF.Bank.bankEnv old).append input) =
      .inl (if (Diamond.read Loop.MLIR.CF.model g.predicate args locals).down then
        ⟨.dispatch 0, readLive args locals wires⟩
      else ⟨.exit, .cons (Diamond.read Loop.MLIR.CF.model g.result args locals) .nil⟩) :=
  Proofs.header_frame g wires plan input old

variable {old new : Nat} {rtlEntry rtlHeader : List (List PortTy)}

/-- The actual CF dispatcher and the checked machine step agree on the successor and full packet. -/
theorem checked_dispatch_step (mapping : InputMap old new) (source : Source old old rtlEntry rtlHeader tests)
    {prog : Prog Reg} (accepted : Family.lowerChecked mapping source = some prog)
    (g : Program new old entrySigs sigs) (wires : Live new old sigs)
    (plan : Plan (lowerFunc (mapCaptures mapping source)) (liveRegs wires) old tests)
    (slot : Fin (tests + 1)) (packet : Env (wordsTy wires.length)) (input : Env (wordsTy new))
    (frame : Frame Reg) (mem : Memory)
    (matched : Snapshot (scope := liveRegs wires) (List.length_map ..) (packet.append input) frame) :
    StepAgreement (bank := old) prog slot frame mem packet
      (((lower g wires plan).block (.dispatch slot)).eval evalOp (fun term env => term.eval env)
        (packet.append input)) :=
  Proofs.checked_dispatch_step mapping source accepted g wires plan slot packet input frame mem matched

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR
