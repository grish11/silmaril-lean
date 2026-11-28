module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern.Defs
public import Silmaril.SSA.SeaOfNodes.Pure.WordNormalize.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Defs

/-! Supply the existing cyclic builder with certified preheader word captures. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader

open Diamond (Dataflow Ty Val ValueSort dataPorts)
open Activation (Inputs inputSlot)
open Pure.SubZero (Opcode model word wordPort)
open GVN.WordNumber.Intern (Id IdVal Table entryIds readId)
open RVSDG (Locals Origin Port Tuple Wires extend)
open Loop (headerPorts)
open scoped Pure.WordNormalize

abbrev Native := Loop.Graph Opcode

variable {inputs carried : List (ValueSort Unit)} {entrySigs headerSigs : List (List (Ty Unit))} {out : ValueSort Unit}

/-- IDs at the actual end of the preheader, all in one table. -/
structure Bank (inputs : List (ValueSort Unit)) (entrySigs : List (List (Ty Unit))) where
  table : Table
  entry : Tuple IdVal (dataPorts inputs)
  locals : Locals IdVal (extend [] entrySigs)

def number (loop : Native inputs carried entrySigs headerSigs out) : Bank inputs entrySigs :=
  let entry := entryIds inputs
  let result := GVN.WordNumber.Intern.eval entry.2 loop.preheader entry.1 PUnit.unit
  ⟨result.1, entry.2, result.2⟩

def laneId (loop : Native inputs carried entrySigs headerSigs out) (bank : Bank inputs entrySigs)
    (lane : Port carried word) : Id :=
  readId bank.entry bank.locals ((loop.phiInputs .entry).get (inputSlot lane))

/-- Word lanes select the first carried position with the same preheader
ID. Predicate lanes keep their own capture position. -/
def canonicalLane (loop : Native inputs carried entrySigs headerSigs out) (bank : Bank inputs entrySigs) :
    {sort : ValueSort Unit} → Port carried sort → Port carried sort
  | .predicate, lane => lane
  | .data (), lane =>
    ((argumentPorts word carried).find? (fun other => decide (laneId loop bank other = laneId loop bank lane))).getD lane

def frontPort {T : Type} {t : T} {right : List T} :
    {left : List T} → Port left t → Port (left ++ right) t
  | _, .head => .head
  | _, .tail port => .tail (frontPort port)

/-- The actual entry tuple is supplied as extra fixed inputs to preparation. -/
def prependValues {F : Ty Unit → Type} {rest : List (ValueSort Unit)} :
    {added : List (ValueSort Unit)} → Tuple F (dataPorts added) → Tuple F (dataPorts rest) →
      Tuple F (dataPorts (added ++ rest))
  | [], .nil, tail => tail
  | _ :: _, .cons value next, tail => .cons value (prependValues next tail)

def preparedInput (loop : Native inputs carried entrySigs headerSigs out) (input : Inputs model inputs) :
    Inputs model (carried ++ inputs) :=
  prependValues (loop.initial model input) input

def entryWires (loop : Native inputs carried entrySigs headerSigs out) (bank : Bank inputs entrySigs) :
    (lanes : List (ValueSort Unit)) → (∀ {sort}, Port lanes sort → Port carried sort) →
    Wires (dataPorts (carried ++ inputs)) [] (dataPorts lanes)
  | [], _ => .nil
  | _ :: rest, lift =>
    .cons (.arg (inputSlot (frontPort (canonicalLane loop bank (lift .head)))))
      (entryWires loop bank rest (fun port => lift (.tail port)))

def liftHeaderPort {t : Ty Unit} : (added : List (ValueSort Unit)) → Port (headerPorts inputs carried) t →
    Port (headerPorts (added ++ inputs) carried) t
  | [], port => port
  | _ :: rest, port => .tail (liftHeaderPort rest port)

def dropHeaderPort? {t : Ty Unit} : (added : List (ValueSort Unit)) → Port (headerPorts (added ++ inputs) carried) t →
    Option (Port (headerPorts inputs carried) t)
  | [], port => some port
  | _ :: _, .head => none
  | _ :: rest, .tail port => dropHeaderPort? rest port

abbrev ObservationPorts (carried : List (ValueSort Unit)) (out : ValueSort Unit) :=
  (.value .predicate : Ty Unit) :: .value out :: dataPorts carried

def observations (loop : Native inputs carried entrySigs headerSigs out) :
    Wires (headerPorts inputs carried) (extend [] headerSigs) (ObservationPorts carried out) :=
  .cons loop.predicate (.cons loop.result (loop.phiInputs .backedge))

def observationTail {args : List (Ty Unit)} {past : List (List (Ty Unit))} :
    Wires args past (ObservationPorts carried out) → Wires args past (dataPorts carried)
  | .cons _ (.cons _ feedback) => feedback

def headerInputs (added : List (ValueSort Unit)) :
    Wires (headerPorts (added ++ inputs) carried) [] (headerPorts inputs carried) :=
  (RVSDG.NestedTheta.identityPorts (headerPorts inputs carried)).map fun _ port =>
    .arg (liftHeaderPort added port)

/-- Present the native header to the existing direct-entry builder.
The lifted header can read the old arguments and latches, and the new
capture arguments enter only through the checked entry column. -/
def prepare (loop : Native inputs carried entrySigs headerSigs out) :
    Native (carried ++ inputs) carried [] headerSigs out :=
  let header := Elimination.plug loop.header (observations loop) (headerInputs carried)
  { preheader := .nil
    header := header.1
    phiInputs
      | .entry => entryWires loop (number loop) carried (fun port => port)
      | .backedge => observationTail header.2
    predicate := header.2.get .head
    result := header.2.get (.tail .head) }

def stripWire? (added : List (ValueSort Unit)) {past : List (List (Ty Unit))} {t : Ty Unit} :
    Origin (headerPorts (added ++ inputs) carried) past t →
    Option (Origin (headerPorts inputs carried) past t)
  | .arg port => (dropHeaderPort? added port).map Origin.arg
  | .output i port => some (.output i port)

def stripWires? (added : List (ValueSort Unit)) {past : List (List (Ty Unit))} :
    {ports : List (Ty Unit)} → Wires (headerPorts (added ++ inputs) carried) past ports →
      Option (Wires (headerPorts inputs carried) past ports)
  | _, .nil => some .nil
  | _, .cons head tail => do
    let head ← stripWire? added head
    let tail ← stripWires? added tail
    pure (.cons head tail)

def stripFlow? (added : List (ValueSort Unit)) : {past sigs : List (List (Ty Unit))} →
    Dataflow Opcode (headerPorts (added ++ inputs) carried) past sigs →
    Option (Dataflow Opcode (headerPorts inputs carried) past sigs)
  | _, _, .nil => some .nil
  | scope, _, .cons (out := sort) op wires rest => do
    let wires ← stripWires? added wires
    let rest ← stripFlow? added (past := scope ++ [[.value sort]]) rest
    pure (.cons op wires rest)

/-- Restore the original input interface only if every surviving header
read, guard, feedback field and exit read is independent of the captures. -/
def restore? (loop : Native inputs carried entrySigs headerSigs out)
    (edited : Deletion.DeletedLoop Opcode (carried ++ inputs) carried [] out) :
    Option (Deletion.DeletedLoop Opcode inputs carried entrySigs out) := do
  let header ← stripFlow? carried edited.graph.header
  let packet ← stripWires? carried (observations edited.graph)
  pure ⟨edited.headerSigs, {
    preheader := loop.preheader
    header := header
    phiInputs
      | .entry => loop.phiInputs .entry
      | .backedge => observationTail packet
    predicate := packet.get .head
    result := packet.get (.tail .head) }⟩

/-- Build and run the existing shrinking pass, then check that its result
can be restored to the original native interface. -/
def optimize? (loop : Native inputs carried entrySigs headerSigs out) :
    Option (Deletion.DeletedLoop Opcode inputs carried entrySigs out) := do
  let built ← build? (prepare loop)
  let edited ← Pass.step? built.view
  restore? loop edited

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader
