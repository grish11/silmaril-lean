module

public import Silmaril.SSA.PEG.Semantics.Defs

/-! # Checked dependency-closed PEG projections

A selection keeps an injectively numbered subset of rows. Its ordered
operands and designated roots must all be in the selection, including
both arms of a φ, initial and feedback θ operands, and eval's pass
operand. All loop IDs and parents are kept. Use `Graph.withRoots` to
select the observations before projecting.
-/

@[expose] public section

namespace Silmaril.SSA.PEG

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}

namespace Projection

abbrev Rows (n : Nat) := List (Fin n)

def Rows.embed (rows : Rows n) (i : Fin rows.length) : Fin n :=
  rows.get i

def pushRef {sort : Fin n → Ty Data} {t : Ty Data} (rows : Rows n)
    (ref : Ref (sort ∘ rows.embed) t) : Ref sort t :=
  ⟨rows.embed ref.id, ref.typed⟩

structure Wires {sort : Fin n → Ty Data} {ts : List (Ty Data)} (rows : Rows n)
    (original : Tuple (Ref sort) ts) where
  refs : Tuple (Ref (sort ∘ rows.embed)) ts
  agrees : refs.map (fun _ => pushRef rows) = original

def findRow (rows : Rows n) (old : Fin n) : Option {i : Fin rows.length // rows.embed i = old} :=
  (List.finRange rows.length).findSome? fun i =>
    if h : rows.embed i = old then some ⟨i, h⟩ else none

def Wires.check {sort : Fin n → Ty Data} (rows : Rows n) :
    {ts : List (Ty Data)} → (original : Tuple (Ref sort) ts) → Option (Wires rows original)
  | _, .nil => some ⟨.nil, rfl⟩
  | _, .cons r rs => do
    let some ⟨i, h⟩ := findRow rows r.id | none
    let some tail := check rows rs | none
    let ref : Ref (sort ∘ rows.embed) _ := ⟨i, (congrArg sort h).trans r.typed⟩
    have head : pushRef rows ref = r := by cases r; cases h; rfl
    return ⟨.cons ref tail.refs, congrArg₂ Tuple.cons head tail.agrees⟩

end Projection

structure Graph.Projection (g : Graph P params results n l) where
  rows : Projection.Rows n
  unique : rows.Nodup
  args : ∀ i : Fin rows.length, Projection.Wires rows (g.node (rows.embed i)).args
  roots : Projection.Wires rows g.roots

variable {g : Graph P params results n l}

/-- Validate an explicit row selection independently of how it was found. -/
def Graph.checkProjection (g : Graph P params results n l) (rows : Projection.Rows n) :
    Option g.Projection := do
  if unique : rows.Nodup then
    let some roots := Projection.Wires.check rows g.roots | none
    let args (i : Fin rows.length) := Projection.Wires.check rows (g.node (rows.embed i)).args
    if closed : ∀ i, (args i).isSome then
      return ⟨rows, unique, fun i => (args i).get (closed i), roots⟩
    else none
  else none

def RankComponent.project (c : RankComponent n l) (rows : Projection.Rows n) :
    RankComponent rows.length l :=
  match c with
  | .phase height => .phase (height ∘ rows.embed)
  | .counter key => .counter key

namespace Graph.Projection

def graph (p : g.Projection) : Graph P params results p.rows.length l where
  forest := g.forest
  sort := g.sort ∘ p.rows.embed
  node i := ⟨(g.node (p.rows.embed i)).inputs, (g.node (p.rows.embed i)).label, (p.args i).refs⟩
  roots := p.roots.refs

def request (p : g.Projection) (q : Request p.rows.length l) : Request n l :=
  (p.rows.embed q.1, q.2)

def valuation (p : g.Projection) (m : Interpretation.{u,v,w} P) (values : g.Valuation m) :
    p.graph.Valuation m :=
  fun q => values (p.request q)

def rank (p : g.Projection) (r : DemandRank n l) : DemandRank p.rows.length l :=
  r.map fun component => component.project p.rows

end Graph.Projection

namespace Projection

/-- Each fresh row adds its complete operand list. Revisited rows do
not expand, even on a recurrent edge. -/
def visit (g : Graph P params results n l) :
    Nat → List (Fin n) → List (Fin n) → Option (List (Fin n))
  | _, [], seen => some seen
  | 0, _ :: _, _ => none
  | fuel + 1, row :: pending, seen =>
    if row ∈ seen then visit g fuel pending seen
    else
      let node := g.node row
      let operands := (List.finRange node.inputs.length).map fun slot => (node.arg slot).id
      visit g fuel (operands ++ pending) (row :: seen)
termination_by structural fuel _ _ => fuel

/-- Candidate closure of the designated roots and extra anchors, returned
in input order. Each operand occurrence is enqueued at most once per row.
Admission still goes through `Graph.checkProjection`. -/
def dependencyRows (g : Graph P params results n l) (anchors : List (Fin n) := []) :
    Option (Rows n) := do
  let all := List.finRange n
  let roots := (List.finRange results.length).map fun i => (g.roots.get (portAt results i)).id
  let seeds := roots ++ anchors
  let edgeCount := (all.map fun i => (g.node i).inputs.length).sum
  let seen ← visit g (seeds.length + edgeCount) seeds []
  return all.filter (fun i => i ∈ seen)

end Projection

end Silmaril.SSA.PEG
