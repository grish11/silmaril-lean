module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Defs

/-! A checked numbered boundary for the returned word, captures and live heap. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary

open RVSDG (Origin Port Tuple Wires)
open RVSDG.OrderedRuntime.Structured (Data Threaded runtimePort withRuntime)
open RVSDG.NestedTheta.ExplicitRuntime (EntryChecked Checked)
open Memory.Diamond.Institution (PortMap pullInput)

variable {ambient next : List ValueSort} {cells : Nat}

/-- Exactly one word capture reads the first return. All other captures
read named typed ports of the ambient input. -/
inductive Wiring (ambient : List ValueSort) : List ValueSort → Type
  | word {rest : List ValueSort} (ports : PortMap rest ambient) : Wiring ambient (.word :: rest)
  | forward {sort : ValueSort} {rest : List ValueSort}
      (port : Port ambient sort) (restWiring : Wiring ambient rest) : Wiring ambient (sort :: rest)

def Wiring.wordPort : {next : List ValueSort} → Wiring ambient next → Port next .word
  | _, .word _ => .head
  | _, .forward _ rest => .tail rest.wordPort

def Wiring.port {sort : ValueSort} :
    {next : List ValueSort} → Wiring ambient next → Port next sort → Port (.word :: ambient) sort
  | _, .word _, .head => .head
  | _, .word ports, .tail p => .tail (ports p)
  | _, .forward p _, .head => .tail p
  | _, .forward _ wiring, .tail p => wiring.port p

/-- Reindex ambient captures while retaining the designated returned-word lane. -/
def Wiring.map {target : List ValueSort} (rename : PortMap ambient target) :
    {next : List ValueSort} → Wiring ambient next → Wiring target next
  | _, .word ports => .word (fun p => rename (ports p))
  | _, .forward p rest => .forward (rename p) (rest.map rename)

/-- The second capture tuple in the sequential observer of the two emitted loops. -/
def Wiring.select (wiring : Wiring ambient next) (word : Word) (captures : Tuple (Val cells) ambient) :
    Tuple (Val cells) next :=
  pullInput wiring.port (.cons word captures)

/-- A reserved word followed by the typed captures and the entire live heap. -/
def packet (word : Word) (captures : Tuple (Val cells) ambient) (heap : Heap cells) :
    Tuple (WireVal cells) (carrier (.word :: ambient)) :=
  encodeInput heap (Tuple.cons (F := Val cells) (t := ValueSort.word) word captures)

def captureWires (entry : List ValueSort) : (sorts : List ValueSort) → PortMap sorts entry →
    Wires (carrier entry) [] (dataPorts sorts)
  | [], _ => .nil
  | _ :: rest, ports =>
    .cons (.arg (argumentPort (ports .head))) (captureWires entry rest (fun p => ports (.tail p)))

/-- The leading output word is reserved for the final pair. The selected
right capture gets its own word lane, alongside forwarded captures. -/
def adapterWires (wiring : Wiring ambient next) :
    Wires (carrier (.word :: ambient)) [] (dataPorts (.word :: next)) :=
  .cons (.arg .head) (captureWires (.word :: ambient) next wiring.port)

def adapterTerm (wiring : Wiring ambient next) :
    RVSDG.NestedTheta.Term ThetaOpcode (carrier (.word :: ambient)) [] [] (carrier (.word :: next)) :=
  .ret (withRuntime (.arg (runtimePort (dataPorts (.word :: ambient)))) (adapterWires wiring))

def adapter (wiring : Wiring ambient next) :
    RVSDG.NestedTheta.Graph ThetaOpcode (carrier (.word :: ambient)) [] [] (carrier (.word :: next)) :=
  (adapterTerm wiring).toGraph

def checked (wiring : Wiring ambient next) :
    EntryChecked (P := TailTest) (E := Effect)
      (a := inputData (.word :: ambient)) (b := inputData (.word :: next)) (adapter wiring).toTerm :=
  (RVSDG.NestedTheta.Term.toTerm_toGraph (adapterTerm wiring)).symm ▸
    Checked.ret (.arg (runtimePort (dataPorts (.word :: ambient)))) (adapterWires wiring)

/-- A checked consumer sees the reserved word and its typed capture tuple,
with the single live heap threaded by the existing numbered splice. -/
def splice (wiring : Wiring ambient next) {outs : List (RVSDG.OrderedRuntime.Structured.Ty ValueSort)}
    {data : Data outs} {sigs : List (List (RVSDG.OrderedRuntime.Structured.Ty ValueSort))}
    {consumer : RVSDG.NestedTheta.Graph ThetaOpcode (carrier (.word :: next)) [] sigs (Threaded outs)}
    (consumerChecked : EntryChecked (a := inputData (.word :: next)) (b := data)
      consumer.toTerm) :
    RVSDG.NestedTheta.Graph ThetaOpcode (carrier (.word :: ambient)) [] sigs (Threaded outs) :=
  RVSDG.NestedTheta.ExplicitRuntime.Splice.graph (checked wiring) consumerChecked

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary
