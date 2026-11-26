module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Defs

/-! A checked straight-line preheader for native guarded rows. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table

open Silmaril.Machine.RTL.SSA (Block Func Op Prog)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp emitOpsWithResults)
open Silmaril.SSA.RVSDG (Address)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

/-- Check every producer. Its operands already belong to the current typed
prefix, which contains captures and earlier results. -/
def supported {arity : Nat} : {past sigs : List (List PortTy)} →
    Dataflow WordOp (wordPorts arity) past sigs → Bool
  | _, _, .nil => true
  | _, _, .cons op _ rest =>
    match op with
    | .add | .sub => supported rest
    | .const _ | .eq | .ne | .slt => false

structure Plan (arity : Nat) (entrySigs : List (List PortTy)) where
  flow : Dataflow WordOp (wordPorts arity) [] entrySigs
  arithmetic : supported flow = true
  entry : EntryColumnWith arity entrySigs
  row : Rows.Plan arity

variable {arity : Nat} {entrySigs : List (List PortTy)} (p : Plan arity entrySigs)

def Plan.graph : SourceWithEntry arity entrySigs p.row.sigs :=
  withEntry p.row.graph p.flow p.entry

/-- Keep captures in their argument registers. Preheader producer registers
follow the argument ranges used by the captures and the carried bank. -/
def resultReg (arity index : Nat) : Reg := .arg (arity + arity + index)

def entryReg (arity : Nat) : Address → Reg
  | .arg i => .arg i
  | .output i _ => resultReg arity i

/-- Emit the ordinary ordered producer table in the preheader register range. -/
def emit {past sigs : List (List PortTy)} (flow : Dataflow WordOp (wordPorts arity) past sigs) :
    List (Op Reg) :=
  emitOpsWithResults (fun port => .arg port.index) (resultReg arity) flow

def Plan.preheader : Block Reg :=
  ⟨paramRegs 0 arity, emit p.flow, .jump 1 (p.entry.addresses.map (entryReg arity))⟩

def Plan.lowerFunc : Func Reg := lowerBankFuncFrom p.row.graph p.preheader
def Plan.rtl : Prog Reg := lowerBankFrom p.row.graph p.preheader

/-- One instruction per producer and one jump to latch the entry bank. -/
def Plan.entrySteps (_ : Plan arity entrySigs) : Nat := entrySigs.length + 1

def Plan.rtlFuel (backedges : Nat) : Nat := p.row.rtlFuel backedges + entrySigs.length

/-- The entry gate requires at least one computed initializer. -/
def isComputedEntry : Address → Bool
  | .output _ _ => true
  | .arg _ => false

/-- The body recognizer uses an argument placeholder for a computed initializer. -/
def entryPlaceholder : Address → Nat
  | .arg i => i
  | .output _ _ => 0

/-- Keep the actual source entry column. Use a checked argument-only column
solely to recover the shared header plan through the existing recognizer. -/
def recognize {sigs : List (List PortTy)} (g : SourceWithEntry arity entrySigs sigs) :
    Option (Plan arity entrySigs) :=
  let entry := g.phiInputs .entry
  if h : supported g.preheader = true then
    if entry.addresses.any isComputedEntry then
      (checkColumn arity arity (entry.addresses.map entryPlaceholder)).bind fun column =>
        (Native.recognize (bodyGraph g column)).bind fun spec =>
          (Rows.checkPlan arity spec).map fun row => ⟨g.preheader, h, entry, row⟩
    else none
  else none

def lowerChecked {sigs : List (List PortTy)} (g : SourceWithEntry arity entrySigs sigs) :
    Option Checked.Phi.Targets :=
  (recognize g).bind fun p =>
    if p.lowerFunc.WellFormed then some (p.rtl, Generic.lower g) else none

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table
