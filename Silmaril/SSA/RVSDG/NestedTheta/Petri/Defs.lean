module

public import Silmaril.SSA.RVSDG.NestedTheta.Defs
public import Silmaril.SSA.RVSDG.Petri.Defs

/-! Explicit nested firing for the primitive, γ and θ fragment. Data places
retain their colours on reads. A waiting token owns just one live child. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri

universe u v w

open RVSDG.Petri (Tokens Vertex read)

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args head ins outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

/-- The numbered node spine indexes a product of places. Its order is used to
resolve wire addresses. A later vertex may fire while an earlier one is pending. -/
def Marking (m : Model.{u, v, w} Op) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Term Op args past sigs outs → Type (max u w)
  | _, _, _, _, .ret _ => PUnit
  | _, _, _, _, .bind (head := head) node children rest =>
    Vertex (Tuple m.Val head) (fun j => Tuple m.Val node.kind.entry × Marking m (children j)) ×
      Marking m rest

/-- A fresh region has one pending token per vertex and no active children. -/
def pending (m : Model.{u, v, w} Op) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    (term : Term Op args past sigs outs) → Marking m term
  | _, _, _, _, .ret _ => PUnit.unit
  | _, _, _, _, .bind _ _ rest => (.pending, pending m rest)

/-- Completion needs every local vertex's done token and all result colours. -/
def finished (m : Model.{u, v, w} Op) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    (term : Term Op args past sigs outs) → Tuple m.Val args → Tokens m.Val past →
    Marking m term → Option (Tuple m.Val outs)
  | _, _, _, _, .ret results, entry, tokens, _ => read results entry tokens
  | _, _, _, _, .bind _ _ rest, entry, tokens, marking =>
    match marking.1 with
    | .done output => finished m rest entry (tokens.snoc (output.map fun _ => some)) marking.2
    | .pending | .waiting _ _ => none

/-- A primitive fires directly and publishes its output tuple. -/
def primitive (m : Model.{u, v, w} Op) (kind : Kind Op ins outs)
    (input : Tuple m.Val ins) : Option (Tuple m.Val outs) :=
  match kind with
  | .base shape => RVSDG.Petri.primitive m shape input
  | .theta _ => none

/-- Select the single live child and its initial argument tuple. -/
def activate (m : Model.{u, v, w} Op) :
    {ins outs : Ports (PortType V S)} → (kind : Kind Op ins outs) → Tuple m.Val ins →
    Option (Fin kind.arity × Tuple m.Val kind.entry)
  | _, _, .base shape, input => RVSDG.Petri.select m shape input
  | _, _, .theta _, input => some ((0 : Fin 1), input)

/-- Read a completed child: the left injection publishes, the right restarts
the current θ with updated carried arguments. -/
def route (m : Model.{u, v, w} Op) :
    {ins outs : Ports (PortType V S)} → (kind : Kind Op ins outs) →
    Fin kind.arity → Tuple m.Val kind.exit → Sum (Tuple m.Val outs) (Tuple m.Val ins)
  | _, _, .base shape, arm, output => .inl (RVSDG.Petri.publish m shape arm output)
  | _, _, .theta _, _, returned => match returned with
    | .cons tag next => if tag.down.val == 1 then .inr next else .inl next

/-- A single hierarchical firing. The input and prefix places are read-only here.
`later` exposes only the output places the preceding vertex has actually marked.
`advance` fires inside the live child carried by a waiting token. -/
inductive Fire (m : Model.{u, v, w} Op) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    (term : Term Op args past sigs outs) → Tuple m.Val args → Tokens m.Val past →
    Marking m term → Marking m term → Prop where
  | primitive
      {args head outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
      {node : Node Op args past head} {children : Children (Term Op) node}
      {rest : Term Op args (past ++ [head]) sigs outs}
      {entry : Tuple m.Val args} {tokens : Tokens m.Val past} {tail : Marking m rest}
      {input : Tuple m.Val node.ins} {output : Tuple m.Val head}
      (ready : read node.inputs entry tokens = some input)
      (result : Petri.primitive m node.kind input = some output) :
      Fire m (.bind node children rest) entry tokens (.pending, tail) (.done output, tail)
  | enter
      {args head outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
      {node : Node Op args past head} {children : Children (Term Op) node}
      {rest : Term Op args (past ++ [head]) sigs outs}
      {entry : Tuple m.Val args} {tokens : Tokens m.Val past} {tail : Marking m rest}
      {input : Tuple m.Val node.ins} {arm : Fin node.kind.arity}
      {received : Tuple m.Val node.kind.entry}
      (ready : read node.inputs entry tokens = some input)
      (guard : activate m node.kind input = some (arm, received)) :
      Fire m (.bind node children rest) entry tokens (.pending, tail)
        (.waiting arm (received, pending m (children arm)), tail)
  | advance
      {args head outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
      {node : Node Op args past head} {children : Children (Term Op) node}
      {rest : Term Op args (past ++ [head]) sigs outs}
      {entry : Tuple m.Val args} {tokens : Tokens m.Val past} {tail : Marking m rest}
      {arm : Fin node.kind.arity} {received : Tuple m.Val node.kind.entry}
      {before after : Marking m (children arm)}
      (step : Fire m (past := []) (children arm) received PUnit.unit before after) :
      Fire m (.bind node children rest) entry tokens (.waiting arm (received, before), tail)
        (.waiting arm (received, after), tail)
  | commit
      {args head outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
      {node : Node Op args past head} {children : Children (Term Op) node}
      {rest : Term Op args (past ++ [head]) sigs outs}
      {entry : Tuple m.Val args} {tokens : Tokens m.Val past} {tail : Marking m rest}
      {arm : Fin node.kind.arity} {received : Tuple m.Val node.kind.entry}
      {child : Marking m (children arm)} {returned : Tuple m.Val node.kind.exit}
      {output : Tuple m.Val head}
      (ready : finished m (past := []) (children arm) received PUnit.unit child = some returned)
      (decision : route m node.kind arm returned = .inl output) :
      Fire m (.bind node children rest) entry tokens (.waiting arm (received, child), tail)
        (.done output, tail)
  | restart
      {args head outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
      {node : Node Op args past head} {children : Children (Term Op) node}
      {rest : Term Op args (past ++ [head]) sigs outs}
      {entry : Tuple m.Val args} {tokens : Tokens m.Val past} {tail : Marking m rest}
      {arm : Fin node.kind.arity} {received next : Tuple m.Val node.kind.entry}
      {child : Marking m (children arm)} {returned : Tuple m.Val node.kind.exit}
      {feedback : Tuple m.Val node.ins}
      (ready : finished m (past := []) (children arm) received PUnit.unit child = some returned)
      (decision : route m node.kind arm returned = .inr feedback)
      (entered : activate m node.kind feedback = some (arm, next)) :
      Fire m (.bind node children rest) entry tokens (.waiting arm (received, child), tail)
        (.waiting arm (next, pending m (children arm)), tail)
  | later
      {args head outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
      {node : Node Op args past head} {children : Children (Term Op) node}
      {rest : Term Op args (past ++ [head]) sigs outs}
      {entry : Tuple m.Val args} {tokens : Tokens m.Val past}
      {vertex : Vertex (Tuple m.Val head)
        (fun j => Tuple m.Val node.kind.entry × Marking m (children j))}
      {before after : Marking m rest}
      (step : Fire m rest entry (tokens.snoc vertex.outputs) before after) :
      Fire m (.bind node children rest) entry tokens (vertex, before) (vertex, after)

abbrev GraphMarking (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs) :=
  Marking m graph.toTerm

/-- Install the graph's pending control tokens. Each execution supplies its fixed
root argument tokens through the `input` parameter of `Step`. -/
def initial (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs) : GraphMarking m graph :=
  pending m graph.toTerm

abbrev Step (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs) (input : Tuple m.Val args) :=
  Fire m (past := []) graph.toTerm input PUnit.unit

def result (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs) (input : Tuple m.Val args)
    (marking : GraphMarking m graph) : Option (Tuple m.Val outs) :=
  finished m (past := []) graph.toTerm input PUnit.unit marking

/-- A finite sequence of firings reaches a completed marking with the given result. -/
def Finishes (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) : Prop :=
  ∃ marking, Relation.ReflTransGen (Step m graph input) (initial m graph) marking ∧
    result m graph input marking = some output

end Silmaril.SSA.RVSDG.NestedTheta.Petri
