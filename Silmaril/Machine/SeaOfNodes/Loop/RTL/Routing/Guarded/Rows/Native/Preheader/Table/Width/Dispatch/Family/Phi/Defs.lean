module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Defs
public import Silmaril.SSA.PhiView.Defs

/-! Read the resized RTL header's incoming columns into the typed explicit-Φ view. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi

open Silmaril.Machine.Lir (Word)
open Silmaril.Machine
open Silmaril.Machine.RTL (Frame wordTy)
open Silmaril.Machine.RTL.SSA (Func)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg)
open Silmaril.Isotope.LambdaSSA (Terminator)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)
open Silmaril.SSA.PhiView

/-- Entry is first, followed by the feedback occurrences in dispatch order. -/
abbrev Incoming (tests : Nat) := Fin (tests + 2)

def key {tests : Nat} (incoming : Incoming tests) : Nat × Nat :=
  Fin.cases (0, 0) occurrence incoming

def params (width : Nat) : List RTL.Ty := List.replicate width wordTy

/-- A full word packet, using positions in the function's flat register context. -/
inductive Packet (scope : List Reg) : Nat → Type where
  | nil : Packet scope 0
  | cons {width : Nat} : Fin scope.length → Packet scope width → Packet scope (width + 1)

variable {scope : List Reg} {width tests : Nat}

def Packet.registers : {width : Nat} → Packet scope width → List Reg
  | _, .nil => []
  | _, .cons index tail => scope[index] :: tail.registers

def Packet.indices : {width : Nat} → Packet scope width → Fin width → Fin scope.length
  | _, .nil => Fin.elim0
  | _, .cons index tail => Fin.cases index tail.indices

def Packet.arguments (packet : Packet scope width) : Arguments (params scope.length) (params width) :=
  fun i =>
    let index := packet.indices ⟨i.val, by simpa [params] using i.isLt⟩
    ⟨index.val, by
      change (params scope.length)[index.val]? = some ((params width)[i.val]'i.isLt)
      simp [params, index.isLt]⟩

def checkPacket (scope : List Reg) : (width : Nat) → List Reg → Option (Packet scope width)
  | 0, [] => some .nil
  | width + 1, reg :: rest =>
    if found : reg ∈ scope then
      (checkPacket scope width rest).map (.cons ⟨scope.idxOf reg, List.idxOf_lt_length_of_mem found⟩)
    else none
  | _, _ => none

/-- Snapshot the register file before any destination parameter is rebound.
Missing or out-of-range entries are irrelevant under a successful RTL packet read. -/
def snapshot (scope : List Reg) (frame : Frame Reg) : Env Word :=
  fun i => .atom ((scope[i]?.bind frame.get).getD 0)

/-- Recover one actual RTL successor and check that it has the typed header interface. -/
def readColumn (fn : Func Reg) (source : Nat × Nat) : Option (Packet fn.allDefs (fn.paramCount 1)) :=
  match fn.block? source.1 with
  | none => none
  | some block =>
    match block.term.args[source.2]? with
    | some (1, regs) => checkPacket fn.allDefs (fn.paramCount 1) regs
    | _ => none

/-- Evidence that the whole family, including entry, was read from RTL. -/
structure Checked (fn : Func Reg) (tests : Nat) : Type where
  present : ∀ i : Incoming tests, (readColumn fn (key i)).isSome

/-- Run the ordinary RTL checker, then recover every column by its occurrence. -/
def extract (fn : Func Reg) (tests : Nat) : Option (Checked fn tests) :=
  if fn.WellFormed then
    if present : ∀ i : Incoming tests, (readColumn fn (key i)).isSome then some ⟨present⟩
    else none
  else none

variable {fn : Func Reg}

def Checked.column (checked : Checked fn tests) (i : Incoming tests) :
    Packet fn.allDefs (fn.paramCount 1) :=
  (readColumn fn (key i)).get (checked.present i)

/-- Typed normalization of each incoming branch leaf into a flat scalar context.
The index names the original RTL source block and successor via `key`. -/
def Checked.terms (checked : Checked fn tests) (i : Incoming tests) : Terminator (RTL.Opcode []) :=
  .br 1 (packTerm (checked.column i).arguments)

def Checked.edge (checked : Checked fn tests) (i : Incoming tests) : EdgeOcc checked.terms :=
  ⟨i, .jump⟩

def Checked.typing (checked : Checked fn tests) : SourceTyping (τ := RTL.Ty) checked.terms :=
  ⟨fun _ => params fn.allDefs.length, fun _ => .jump⟩

def Checked.blockArgs (checked : Checked fn tests) :
    BlockArgs checked.typing (fun _ => params (fn.paramCount 1)) :=
  fun ⟨i, successor⟩ => by
    cases successor
    exact ⟨(checked.column i).arguments, rfl⟩

def Checked.view (checked : Checked fn tests) :
    View checked.typing (fun _ => params (fn.paramCount 1)) :=
  ofBlockArgs checked.blockArgs

/-- Decode the explicit-Φ column back into machine register operands. -/
def decodeArguments (scope : List Reg) {Γ : List RTL.Ty} :
    {types : List RTL.Ty} → Arguments Γ types → Option (List Reg)
  | [], _ => some []
  | _ :: _, args => scope[(args 0).val]?.bind fun reg =>
      (decodeArguments scope (fun i => args i.succ)).map (reg :: ·)

def Checked.reemit (checked : Checked fn tests) (i : Incoming tests) : Option (Nat × List Reg) :=
  let edge := checked.edge i
  (decodeArguments fn.allDefs (toBlockArgs checked.view edge).val).map fun regs => (edge.target, regs)

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi
