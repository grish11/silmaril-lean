module

public import Silmaril.SSA.RVSDG.Theta.Defs

/-! Typed RVSDG regions with θ at any vertex. Each activation begins in a fresh local scope. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}

inductive Kind (Op : Dialect.{u, v} V S) :
    Ports (PortType V S) → Ports (PortType V S) → Type (max u v) where
  | base {ins outs : Ports (PortType V S)} (shape : Shape Op ins outs) : Kind Op ins outs
  | theta (carried : Ports (PortType V S)) : Kind Op carried carried

variable {args ins head outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

def Kind.arity : {ins outs : Ports (PortType V S)} → Kind Op ins outs → Nat
  | _, _, .base shape => shape.regionCount
  | _, _, .theta _ => 1

def Kind.entry : {ins outs : Ports (PortType V S)} → Kind Op ins outs → Ports (PortType V S)
  | _, _, .base shape => shape.entry
  | _, _, .theta carried => carried

def Kind.exit : {ins outs : Ports (PortType V S)} → Kind Op ins outs → Ports (PortType V S)
  | _, _, .base shape => shape.exit
  | _, _, .theta carried => Theta.BodyResults carried

structure Node (Op : Dialect.{u, v} V S) (args : Ports (PortType V S))
    (past : List (Ports (PortType V S))) (outs : Ports (PortType V S)) where
  ins : Ports (PortType V S)
  kind : Kind Op ins outs
  inputs : Wires args past ins
  childSigs : Fin kind.arity → List (Ports (PortType V S))

abbrev Node.ofBase (node : RVSDG.Node Op args past outs) : Node Op args past outs :=
  ⟨node.ins, .base node.shape, node.inputs, node.childSigs⟩

abbrev Nodes (Op : Dialect.{u, v} V S) (args : Ports (PortType V S))
    (past sigs : List (Ports (PortType V S))) :=
  (i : Fin sigs.length) → Node Op args (site past sigs i).1 (site past sigs i).2

abbrev Children
    (R : Ports (PortType V S) → List (Ports (PortType V S)) → List (Ports (PortType V S)) →
      Ports (PortType V S) → Type w) (node : Node Op args past outs) :=
  (i : Fin node.kind.arity) → R node.kind.entry [] (node.childSigs i) node.kind.exit

/-- Let syntax with ordered bindings. Every γ arm and θ body starts with only its declared arguments. -/
inductive Term (Op : Dialect.{u, v} V S) : (args : Ports (PortType V S)) →
    (past sigs : List (Ports (PortType V S))) → (outs : Ports (PortType V S)) → Type (max u v) where
  | ret {args outs : Ports (PortType V S)} {past : List (Ports (PortType V S))}
      (results : Wires args past outs) : Term Op args past [] outs
  | bind {args head outs : Ports (PortType V S)} {past tail : List (Ports (PortType V S))}
      (node : Node Op args past head)
      (children : (i : Fin node.kind.arity) →
        Term Op node.kind.entry [] (node.childSigs i) node.kind.exit)
      (rest : Term Op args (past ++ [head]) tail outs) : Term Op args past (head :: tail) outs

/-- A numbered vertex table, child-region table and result wiring. Feedback
is at a θ boundary, leaving the local graph acyclic in every region. -/
inductive Graph (Op : Dialect.{u, v} V S) : (args : Ports (PortType V S)) →
    (past sigs : List (Ports (PortType V S))) → (outs : Ports (PortType V S)) → Type (max u v) where
  | region {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
      (nodes : Nodes Op args past sigs)
      (children : (i : Fin sigs.length) → (j : Fin (nodes i).kind.arity) →
        Graph Op (nodes i).kind.entry [] ((nodes i).childSigs j) (nodes i).kind.exit)
      (results : Wires args (extend past sigs) outs) : Graph Op args past sigs outs

def Nodes.cons (node : Node Op args past head) (nodes : Nodes Op args (past ++ [head]) sigs) :
    Nodes Op args past (head :: sigs) :=
  Fin.cases (motive := fun i => Node Op args (site past (head :: sigs) i).1
    (site past (head :: sigs) i).2) node nodes

def Graph.prepend (node : Node Op args past head) (children : Children (Graph Op) node) :
    Graph Op args (past ++ [head]) sigs outs → Graph Op args past (head :: sigs) outs
  | .region nodes regions results =>
    let all := Nodes.cons node nodes
    .region all (Fin.cases (motive := fun i => Children (Graph Op) (all i)) children regions) results

def Term.toGraph : {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Term Op args past sigs outs → Graph Op args past sigs outs
  | _, _, _, _, .ret results => .region (fun i => i.elim0) (fun i => i.elim0) results
  | _, _, _, _, .bind node children rest => rest.toGraph.prepend node (fun j => (children j).toGraph)

def Term.fromTable {args outs : Ports (PortType V S)} (past : List (Ports (PortType V S))) :
    (sigs : List (Ports (PortType V S))) → (nodes : Nodes Op args past sigs) →
    ((i : Fin sigs.length) → Children (Term Op) (nodes i)) →
    Wires args (extend past sigs) outs → Term Op args past sigs outs
  | [], _, _, results => .ret results
  | head :: rest, nodes, children, results =>
    .bind (nodes 0) (children 0)
      (fromTable (past ++ [head]) rest (fun i => nodes i.succ) (fun i => children i.succ) results)

def Graph.toTerm : {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Graph Op args past sigs outs → Term Op args past sigs outs
  | _, _, _, _, .region nodes children results =>
    Term.fromTable _ _ nodes (fun i j => (children i j).toTerm) results

def Term.ofBase : {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    RVSDG.Term Op args past sigs outs → Term Op args past sigs outs
  | _, _, _, _, .ret results => .ret results
  | _, _, _, _, .bind node children rest =>
    .bind (.ofBase node) (fun j => ofBase (children j)) (ofBase rest)

def Graph.ofBase : {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    RVSDG.Graph Op args past sigs outs → Graph Op args past sigs outs
  | _, _, _, _, .region nodes children results =>
    .region (fun i => .ofBase (nodes i)) (fun i j => ofBase (children i j)) results

/-- Positional ports as a typed tuple. -/
def identityPorts {Ty : Type u} : (ts : Ports Ty) → Tuple (Port ts) ts
  | [] => .nil
  | _ :: rest => .cons .head ((identityPorts rest).map fun _ => .tail)

abbrev thetaVertex {carried : Ports (PortType V S)} (bodySigs : List (Ports (PortType V S))) :
    Node Op carried [] carried :=
  ⟨carried, .theta carried, (identityPorts carried).map fun _ => .arg, fun _ => bodySigs⟩

/-- The ordered results of the sole vertex of an embedded whole-region θ. -/
def thetaResults {Ty : Type u} (carried : Ports Ty) : Wires carried [carried] carried :=
  (identityPorts carried).map fun _ => Origin.output (past := [carried]) (0 : Fin 1)

def Term.ofTheta (theta : Theta.Term Op args sigs) : Term Op args [] [args] args :=
  .bind (thetaVertex sigs) (fun _ => .ofBase theta.body) (.ret (thetaResults args))

def Graph.ofTheta (theta : Theta.Graph Op args sigs) : Graph Op args [] [args] args :=
  .region (Fin.cases (thetaVertex sigs) (fun i => i.elim0))
    (Fin.cases (fun _ => .ofBase theta.body) (fun i => i.elim0)) (thetaResults args)

/-- Bound the number of body activations at a single θ invocation.
The body itself receives its own bound at each activation. -/
def iterate {F : PortType V S → Type w} {carried : Ports (PortType V S)}
    (body : Tuple F carried → Option (Tuple F (Theta.BodyResults carried)))
    (branch : F (.control 2) → Bool) :
    Nat → Tuple F carried → Option (Tuple F carried)
  | 0, _ => none
  | fuel + 1, input =>
    match body input with
    | none => none
    | some (.cons control next) => if branch control then iterate body branch fuel next else some next

def Kind.eval (m : Model.{u, v, w} Op) (fuel : Nat) :
    {ins outs : Ports (PortType V S)} → (kind : Kind Op ins outs) →
    (Fin kind.arity → Tuple m.Val kind.entry → Option (Tuple m.Val kind.exit)) →
    Tuple m.Val ins → Option (Tuple m.Val outs)
  | _, _, .base (.simple opcode), _, input => some (m.run opcode input)
  | _, _, .base (.gamma _), child, .cons tag entry => child tag.down entry
  | _, _, .theta _, child, input => iterate (child (0 : Fin 1)) (fun tag => tag.down.val == 1) fuel input

/-- Execute each let, with fresh environments at subregion entry. -/
def Term.eval (m : Model.{u, v, w} Op) (fuel : Nat) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Tuple m.Val args → Locals m.Val past → Term Op args past sigs outs → Option (Tuple m.Val outs)
  | _, _, _, _, entry, locals, .ret results => some (results.read entry locals)
  | _, _, _, _, entry, locals, .bind node children rest => do
    let result ← node.kind.eval m fuel
      (fun i input => (children i).eval m fuel (past := []) input PUnit.unit) (node.inputs.read entry locals)
    rest.eval m fuel entry (locals.snoc result)

abbrev Runners (m : Model.{u, v, w} Op) (nodes : Nodes Op args past sigs) :=
  (i : Fin sigs.length) → Fin (nodes i).kind.arity →
    Tuple m.Val (nodes i).kind.entry → Option (Tuple m.Val (nodes i).kind.exit)

def evalTable (m : Model.{u, v, w} Op) (fuel : Nat) (entry : Tuple m.Val args) :
    (past sigs : List (Ports (PortType V S))) → Locals m.Val past →
    (nodes : Nodes Op args past sigs) → Runners m nodes →
    Wires args (extend past sigs) outs → Option (Tuple m.Val outs)
  | _, [], locals, _, _, results => some (results.read entry locals)
  | past, head :: rest, locals, nodes, child, results => do
    let node := nodes 0
    let result ← node.kind.eval m fuel (child 0) (node.inputs.read entry locals)
    evalTable m fuel entry (past ++ [head]) rest (locals.snoc result)
      (fun i => nodes i.succ) (fun i => child i.succ) results

/-- Evaluate the numbered graph table directly. Only θ feedback consumes this bound. -/
def Graph.eval (m : Model.{u, v, w} Op) (fuel : Nat) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Tuple m.Val args → Locals m.Val past → Graph Op args past sigs outs → Option (Tuple m.Val outs)
  | _, _, _, _, entry, locals, .region nodes children results =>
    evalTable m fuel entry _ _ locals nodes
      (fun i j input => (children i j).eval m fuel (past := []) input PUnit.unit) results

def Term.run (t : Term Op args [] sigs outs) (m : Model.{u, v, w} Op) (fuel : Nat)
    (input : Tuple m.Val args) : Option (Tuple m.Val outs) :=
  t.eval m fuel (past := []) input PUnit.unit

def Graph.run (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op) (fuel : Nat)
    (input : Tuple m.Val args) : Option (Tuple m.Val outs) :=
  g.eval m fuel (past := []) input PUnit.unit

/-- The local finite-return rule. A θ executes a complete body at every restart. -/
def Kind.Exec (m : Model.{u, v, w} Op) :
    {ins outs : Ports (PortType V S)} → (kind : Kind Op ins outs) →
    (Fin kind.arity → Tuple m.Val kind.entry → Tuple m.Val kind.exit → Prop) →
    Tuple m.Val ins → Tuple m.Val outs → Prop
  | _, _, .base (.simple opcode), _, input, output => m.run opcode input = output
  | _, _, .base (.gamma _), child, .cons tag entry, output => child tag.down entry output
  | _, _, .theta _, child, input, output =>
    Theta.Iterate (fun x keepGoing y => child (0 : Fin 1) x (Theta.bodyResult m keepGoing y)) input output

/-- Finite execution of the inductive syntax, specified without an iteration bound. -/
def Term.Exec (m : Model.{u, v, w} Op) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Term Op args past sigs outs → Tuple m.Val args → Locals m.Val past → Tuple m.Val outs → Prop
  | _, _, _, _, .ret wires, entry, locals, output => wires.read entry locals = output
  | _, _, _, _, .bind node children rest, entry, locals, output =>
    ∃ result, node.kind.Exec m (fun i x y => (children i).Exec m (past := []) x PUnit.unit y)
      (node.inputs.read entry locals) result ∧ rest.Exec m entry (locals.snoc result) output

def Term.Returns (t : Term Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) : Prop :=
  t.Exec m (past := []) input PUnit.unit output

/-- A graph returns a tuple when its direct table evaluator succeeds at some finite bound. -/
def Graph.Returns (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) : Prop :=
  ∃ fuel, g.run m fuel input = some output

end Silmaril.SSA.RVSDG.NestedTheta
