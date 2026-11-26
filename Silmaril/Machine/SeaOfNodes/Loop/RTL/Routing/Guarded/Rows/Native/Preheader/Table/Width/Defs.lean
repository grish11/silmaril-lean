module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Reindex.Defs

/-! Separate an external word interface from the loop's carried bank. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width

open Silmaril.Machine.RTL.SSA (Block Func Prog)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp word emitOpsWith emitOpsWithResults)
open Silmaril.SSA.RVSDG (Port Address)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow)
open Silmaril.SSA.SeaOfNodes.Loop (Graph)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

abbrev Source (captures bank : Nat) (entrySigs sigs : List (List PortTy)) :=
  Graph WordOp (wordSorts captures) (wordSorts bank) entrySigs sigs word

variable {old new bank : Nat} {entrySigs sigs : List (List PortTy)}

/-- Map the capture prefix of a header and retain each position of the bank suffix. -/
def mapPrefix {target bank : List PortTy} : {source : List PortTy} →
    (∀ {t}, Port source t → Port target t) → ∀ {t}, Port (source ++ bank) t → Port (target ++ bank) t
  | [], _, _, p => suffixPort target p
  | _ :: _, mapping, _, .head => prefixPort (mapping .head)
  | _ :: _, mapping, _, .tail p => mapPrefix (fun port => mapping (.tail port)) p

def mapFlow {source target : List PortTy} (mapping : ∀ {t}, Port source t → Port target t) :
    {past sigs : List (List PortTy)} → Dataflow WordOp source past sigs → Dataflow WordOp target past sigs
  | _, _, .nil => .nil
  | _, _, .cons op args rest => .cons op (mapColumn (fun p => mapping p) args) (mapFlow (fun p => mapping p) rest)

def headerPort (mapping : InputMap old new) {t : PortTy} :
    Port (wordPorts old ++ wordPorts bank) t → Port (wordPorts new ++ wordPorts bank) t :=
  mapPrefix (fun p => mapping.port p)

/-- Rewrite both capture scopes of the actual graph. Producer numbers, bank
positions and the distinct entry and feedback occurrences keep their order. -/
def mapCaptures (mapping : InputMap old new) (g : Source old bank entrySigs sigs) :
    Source new bank entrySigs sigs :=
  let headerMap := fun {t} (p : Port (wordPorts old ++ wordPorts bank) t) => headerPort mapping p
  { preheader := mapFlow (fun p => mapping.port p) g.preheader
    header := mapFlow headerMap g.header
    phiInputs
      | .entry => mapping.column (g.phiInputs .entry)
      | .backedge => mapColumn headerMap (g.phiInputs .backedge)
    predicate := mapOrigin headerMap g.predicate
    result := mapOrigin headerMap g.result }

/-- Entry temporaries follow both the capture and bank parameter ranges. -/
def resultReg (captures bank index : Nat) : Reg := .arg (captures + bank + index)

def entryReg (captures bank : Nat) : Address → Reg
  | .arg index => .arg index
  | .output index _ => resultReg captures bank index

def preheader {captures : Nat} (g : Source captures bank entrySigs sigs) : Block Reg :=
  ⟨paramRegs 0 captures, emitOpsWithResults (fun p => .arg p.index) (resultReg captures bank) g.preheader,
    .jump 1 ((g.phiInputs .entry).addresses.map (entryReg captures bank))⟩

def header {captures : Nat} (g : Source captures bank entrySigs sigs) : Block Reg :=
  ⟨paramRegs captures bank, emitOpsWith (fun p => .arg p.index) g.header,
    .cond (register g.predicate.address) 1 (emitColumn (arity := bank) (g.phiInputs .backedge))
      2 [register g.result.address]⟩

def lowerFunc {captures : Nat} (g : Source captures bank entrySigs sigs) : Func Reg :=
  ⟨⟨captures, 1⟩, 0, [preheader g, header g, exitBlock]⟩

def lowerRTL {captures : Nat} (g : Source captures bank entrySigs sigs) : Prog Reg :=
  ⟨[lowerFunc g]⟩

/-- Entry producers and jump, one header activation per visit, then the return instruction. -/
def rtlFuel (entrySigs sigs : List (List PortTy)) (backedges : Nat) : Nat :=
  entrySigs.length + 1 + ((sigs.length + 1) * (backedges + 1) + 1)

/-- Start from the ordinary checked table. Emit the graph at its new
interface and validate the resulting RTL function with the actual SSA checker. -/
def lowerChecked (mapping : InputMap old new) (g : SourceWithEntry old entrySigs sigs) :
    Option Checked.Phi.Targets := do
  let _ ← Table.lowerChecked g
  let mapped := mapCaptures mapping g
  let fn := lowerFunc mapped
  if fn.WellFormed then some (lowerRTL mapped, Generic.lower mapped) else none

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width
