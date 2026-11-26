module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Defs

/-! Static carried-port support for ranked pure loop producers. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support

open Diamond (Dataflow Signature Ty ValueSort dataPorts)
open RVSDG (Locals Origin Tuple extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {n : Nat} {args : List (Ty Data)} {past sigs : List (List (Ty Data))}

/-- One set of carried port numbers per typed argument or producer result. -/
abbrev Ports (n : Nat) (_ : Ty Data) := Finset (Fin n)

def emptyPorts (n : Nat) : (ports : List (Ty Data)) → Tuple (Ports n) ports
  | [] => .nil
  | _ :: rest => .cons ∅ (emptyPorts n rest)

def numberedPorts : (ports : List (Ty Data)) → (Fin ports.length → Fin n) → Tuple (Ports n) ports
  | [], _ => .nil
  | _ :: rest, number => .cons {number 0} (numberedPorts rest (fun i => number i.succ))

/-- Captured inputs contribute no carried dependencies. Each latch port names itself. -/
def headerPorts (inputs carried : List (ValueSort Data)) :
    Tuple (Ports (dataPorts carried).length) (Loop.headerPorts inputs carried) :=
  appendTuple (numberedPorts (dataPorts carried) id) (emptyPorts _ (dataPorts inputs))

def unions : {ports : List (Ty Data)} → Tuple (Ports n) ports → Finset (Fin n)
  | [], .nil => ∅
  | _ :: _, .cons head rest => head ∪ unions rest

/-- In producer order, assign each result the union of the supports of its
typed operands. A nullary producer has empty support. -/
def table (input : Tuple (Ports n) args) :
    {past sigs : List (List (Ty Data))} → Dataflow Op args past sigs →
    Locals (Ports n) past → Locals (Ports n) (extend past sigs)
  | _, _, .nil, locals => locals
  | past, _, .cons (sigs := tail) (out := out) _ wires rest, locals =>
    let head : List (Ty Data) := [.value out]
    let supported : Tuple (Ports n) head := .cons (unions (wires.read input locals)) .nil
    table input (past := past ++ [head]) (sigs := tail) rest (locals.snoc supported)

def read (input : Tuple (Ports n) args) (locals : Locals (Ports n) past)
    {t : Ty Data} : Origin args past t → Finset (Fin n)
  | .arg port => input.get port
  | .output node port => (locals.get node).get port

def wire {inputs carried : List (ValueSort Data)} (flow : Dataflow Op (Loop.headerPorts inputs carried) [] sigs)
    {t : Ty Data} (origin : Origin (Loop.headerPorts inputs carried) (extend [] sigs) t) :
    Finset (Fin (dataPorts carried).length) :=
  let args := headerPorts inputs carried
  read args (table args flow PUnit.unit) origin

/-- Outside the support, use the same bottom fact in every watch key. -/
def restrictBank {value : Data → Type w} {ports : List (Ty Data)}
    (support : Finset (Fin ports.length)) (bank : BankFacts value ports) : BankFacts value ports :=
  fun i => if i ∈ support then bank i else ⊥

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support
