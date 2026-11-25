module

public import Silmaril.SSA.RVSDG.Defs
public import Mathlib.Logic.Equiv.Defs

/-!
# Isomorphism of typed RVSDG regions

Numeric addresses expose the endpoints already checked by the graph's types.
An isomorphism reindexes vertices, preserving the ordered argument, result,
input, output and arm ports of each region.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG

universe u v

/-- Positions count every port in its tuple, including ports of other types. -/
def Port.index {Ty : Type u} {ts : Ports Ty} {t : Ty} : Port ts t → Nat
  | .head => 0
  | .tail p => p.index + 1

inductive Address where
  | arg (port : Nat)
  | output (vertex port : Nat)
  deriving DecidableEq, Repr

def Address.rename (vertices : Nat → Nat) : Address → Address
  | .arg port => .arg port
  | .output vertex port => .output (vertices vertex) port

def Origin.address {Ty : Type u} {args : Ports Ty} {past : List (Ports Ty)} {t : Ty} :
    Origin args past t → Address
  | .arg p => .arg p.index
  | .output vertex p => .output vertex.val p.index

/-- The origin address of each input or result port, in user-port order. -/
def Wires.addresses {Ty : Type u} {args users : Ports Ty} {past : List (Ports Ty)} :
    Wires args past users → List Address
  | .nil => []
  | .cons source rest => source.address :: addresses rest

/-- Extend a bijection of valid vertex numbers to the address vocabulary. -/
def renameVertex {n k : Nat} (ids : Fin n ≃ Fin k) (vertex : Nat) : Nat :=
  if h : vertex < n then (ids ⟨vertex, h⟩).val else vertex

variable {V S : Type u} {Op : Dialect.{u, v} V S}

/-- A vertex label includes its ordered signatures, node kind and primitive opcode. -/
structure NodeLabel (Op : Dialect.{u, v} V S) where
  ins : Ports (PortType V S)
  outs : Ports (PortType V S)
  shape : Shape Op ins outs

def NodeLabel.arity (label : NodeLabel Op) : Nat := label.shape.regionCount

def Node.label {args outs : Ports (PortType V S)} {past : List (Ports (PortType V S))}
    (node : Node Op args past outs) : NodeLabel Op :=
  ⟨node.ins, outs, node.shape⟩

/-- Hierarchical, typed port-graph isomorphism. Region arguments and results
are fixed by position and type. At each region there is a vertex bijection
preserving labels, all operand and result edges, and every child at its
original arm position. The bijections may change the topological numbering. -/
inductive Graph.Isomorphic {V S : Type u} (Op : Dialect.{u, v} V S) :
    {leftArgs rightArgs leftOut rightOut : Ports (PortType V S)} →
    {leftSigs rightSigs : List (Ports (PortType V S))} →
    Graph Op leftArgs [] leftSigs leftOut → Graph Op rightArgs [] rightSigs rightOut → Prop where
  | intro {leftArgs rightArgs leftOut rightOut : Ports (PortType V S)}
      {leftSigs rightSigs : List (Ports (PortType V S))}
      {left : Graph Op leftArgs [] leftSigs leftOut} {right : Graph Op rightArgs [] rightSigs rightOut}
      (entry : leftArgs = rightArgs) (exit : leftOut = rightOut)
      (ids : Fin leftSigs.length ≃ Fin rightSigs.length)
      (labels : ∀ i, (left.nodes i).label = (right.nodes (ids i)).label)
      (inputs : ∀ i, (left.nodes i).inputs.addresses.map (Address.rename (renameVertex ids)) =
        (right.nodes (ids i)).inputs.addresses)
      (results : left.results.addresses.map (Address.rename (renameVertex ids)) =
        right.results.addresses)
      (children : ∀ i (arm : Fin (left.nodes i).shape.regionCount),
        Graph.Isomorphic Op (left.children i arm)
          (right.children (ids i) (Fin.cast (congrArg NodeLabel.arity (labels i)) arm))) :
      Graph.Isomorphic Op left right

end Silmaril.SSA.RVSDG
