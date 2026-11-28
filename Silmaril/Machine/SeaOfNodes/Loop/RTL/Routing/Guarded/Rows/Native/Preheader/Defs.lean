module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Defs

/-! A computed entry value for a checked native guarded row. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader

open Silmaril.Machine.Lir (Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Block Func Prog)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp emitOpWith model word)
open Silmaril.SSA.RVSDG (Address Wires extend)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow)
open Silmaril.SSA.SeaOfNodes.Loop (Graph)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

abbrev EntrySigs : List (List PortTy) := [[wordPort]]

abbrev SourceWithEntry (arity : Nat) (entrySigs sigs : List (List PortTy)) :=
  Graph WordOp (wordSorts arity) (wordSorts arity) entrySigs sigs word

abbrev EntryColumnWith (arity : Nat) (sigs : List (List PortTy)) :=
  Wires (wordPorts arity) (extend [] sigs) (wordPorts arity)

abbrev Source (arity : Nat) := SourceWithEntry arity EntrySigs
abbrev EntryColumn (arity : Nat) := EntryColumnWith arity EntrySigs

structure Initializer (arity : Nat) where
  operation : FeedbackOp
  operands : Wires (wordPorts arity) [] [wordPort, wordPort]

def Initializer.flow {arity : Nat} (init : Initializer arity) :
    Dataflow WordOp (wordPorts arity) [] EntrySigs :=
  .cons init.operation.source init.operands .nil

def Initializer.value {arity : Nat} (init : Initializer arity) (input : WordTuple arity) : Word :=
  model.run init.operation.source (init.operands.read input PUnit.unit)

def decodeInitializer {arity : Nat} : Dataflow WordOp (wordPorts arity) [] EntrySigs → Option (Initializer arity)
  | .cons .add operands .nil => some ⟨.add, operands⟩
  | .cons .sub operands .nil => some ⟨.sub, operands⟩
  | .cons (.const _) _ .nil => none

/-- Supply a typed entry column to the existing recognizer. The checked
preheader retains the original entry column separately. -/
def bodyGraph {arity : Nat} {entrySigs sigs : List (List PortTy)} (g : SourceWithEntry arity entrySigs sigs)
    (entry : ArgumentColumn arity arity) : BankGraph arity sigs where
  preheader := .nil
  header := g.header
  phiInputs
    | .entry => entry
    | .backedge => g.phiInputs .backedge
  predicate := g.predicate
  result := g.result

/-- The input corresponding to an initializer operand is used as a
placeholder at computed entry slots while recognizing the header. -/
def placeholderEntry {arity : Nat} (init : Initializer arity) (column : EntryColumn arity) :
    Option (ArgumentColumn arity arity) :=
  checkColumn arity arity (column.addresses.map fun
    | .arg i => i
    | .output _ _ =>
      match init.operands.get .head with
      | .arg port => port.index
      | .output i _ => i.elim0)

structure Plan (arity : Nat) where
  initializer : Initializer arity
  entry : EntryColumn arity
  row : Rows.Plan arity

variable {arity : Nat} (p : Plan arity)

def withEntry {entrySigs sigs : List (List PortTy)} (body : BankGraph arity sigs)
    (flow : Dataflow WordOp (wordPorts arity) [] entrySigs) (entry : EntryColumnWith arity entrySigs) :
    SourceWithEntry arity entrySigs sigs where
  preheader := flow
  header := body.header
  phiInputs
    | .entry => entry
    | .backedge => body.phiInputs .backedge
  predicate := body.predicate
  result := body.result

def Plan.graph : Source arity p.row.sigs :=
  withEntry p.row.graph p.initializer.flow p.entry

/-- Input and bank registers occupy the first two ranges. The preheader
temporary occupies the next argument register and is local to entry routing. -/
def initRegister (arity : Nat) : Reg := .arg (arity + arity)

def entryRegister (arity : Nat) : Address → Reg
  | .arg i => .arg i
  | .output _ _ => initRegister arity

def Plan.preheader : Block Reg :=
  ⟨paramRegs 0 arity,
    [emitOpWith (fun port => .arg port.index) (initRegister arity) p.initializer.operation.source p.initializer.operands],
    .jump 1 (p.entry.addresses.map (entryRegister arity))⟩

def Plan.lowerFunc : Func Reg := lowerBankFuncFrom p.row.graph p.preheader
def Plan.rtl : Prog Reg := lowerBankFrom p.row.graph p.preheader

/-- Instruction fuel for a return after this many backedges. The initializer
adds one instruction to the existing entry jump, visits and return. -/
def Plan.rtlFuel (backedges : Nat) : Nat := p.row.rtlFuel backedges + 1

/-- Recognize a single add/sub on captures and require that a bank slot
receives its result. Reuse the empty-entry recognizer for the exact header. -/
def recognize {sigs : List (List PortTy)} (g : Source arity sigs) : Option (Plan arity) :=
  (decodeInitializer g.preheader).bind fun init =>
    let column := g.phiInputs .entry
    if .output 0 0 ∈ column.addresses then
      (placeholderEntry init column).bind fun entry =>
        (Native.recognize (bodyGraph g entry)).bind fun spec =>
          (Rows.checkPlan arity spec).map fun row => ⟨init, column, row⟩
    else none

def lowerChecked {sigs : List (List PortTy)} (g : Source arity sigs) : Option Checked.Phi.Targets :=
  (recognize g).bind fun p =>
    if p.lowerFunc.WellFormed then some (p.rtl, Generic.lower g) else none

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader
