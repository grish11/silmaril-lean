module

public import Silmaril.SSA.PEG.Simple.Revert.Schedule.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Automatic.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Automatic.Defs
public import Silmaril.SSA.PEG.Reindex.Automatic.Defs

/-! # Bounded placement of candidate PEG regions -/

public section

namespace Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic

open RVSDG (Port Tuple)
open While.Region (lookup)
open PEG.Reindex.Automatic (Pairs Task loopTasks refIds)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results args outs before : List (Ty Data)} {n l rows loops : Nat} {t : Ty Data}
abbrev CountedRoles (P : InstructionSet.{u,v} Data) := While.Region.Closed.Automatic.Roles P

/-- Counted stages use the existing zero, tick and negation roles.
A nested-only dialect needs just Boolean negation. -/
inductive Roles (P : InstructionSet.{u,v} Data) where
  | counted : CountedRoles P → Roles P
  | nestedOnly : P [.bool] .bool → Roles P

@[expose] def Roles.negate : Roles P → P [.bool] .bool
  | .counted roles => roles.negate
  | .nestedOnly negate => negate

@[expose] def Roles.Laws (m : Interpretation.{u,v,w} P) : Roles P → Prop
  | .counted roles => roles.Laws m
  | .nestedOnly negate => ∀ b : Bool, m.run negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩

variable {g : Graph P params results n l} {roles : Roles P}

@[expose] def RegionRoles {localGraph : Graph P args outs rows loops} (roles : Roles P) :
    Region localGraph → Prop
  | .closed a => match roles with
    | .counted ops => a.descriptor.zero = ops.zero ∧ a.descriptor.tick = ops.tick ∧
        a.descriptor.negate = ops.negate
    | .nestedOnly _ => False
  | .nested a => a.descriptor.negate = roles.negate

@[expose] def PlanRoles (roles : Roles P) : {args outs : List (Ty Data)} → Plan g args outs → Prop
  | _, _, .done _ => True
  | _, _, .step _ stage tail => RegionRoles roles stage.region ∧ PlanRoles roles tail

/-- Supply checked local regions with candidate interfaces. The search
finds their order and the embedding of each into the original graph. -/
structure Leaf (roles : Roles P) where
  inputs : List (Ty Data)
  outputs : List (Ty Data)
  rows : Nat
  loops : Nat
  graph : Graph P inputs outputs rows loops
  region : Region graph
  roleMatch : RegionRoles roles region

def Leaf.closed [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (roles : CountedRoles P) (graph : Graph P args outs rows 1) : Option (Leaf (.counted roles)) := do
  let a ← While.Region.Closed.Automatic.extract graph roles
  return ⟨args, outs, rows, 1, graph, .closed a.certificate, a.zero, a.tick, a.negate⟩

def Leaf.nested [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (roles : Roles P) (graph : Graph P args [t] rows loops) (rank : DemandRank rows loops) :
    Option (Leaf roles) := do
  let a ← While.Nested.Region.Automatic.extract graph rank roles.negate
  return ⟨args, [t], rows, loops, graph, .nested a.certificate, a.negate_eq⟩

private def entryPass {graph : Graph P args outs rows loops} : Region graph → Fin rows
  | .closed a => a.descriptor.pass.id
  | .nested a => a.descriptor.outerPass.id

inductive Rejection where
  | invalidRank
  | parameterRows
  | budget
  | noPlan
  deriving DecidableEq, Repr

private abbrev Search (α : Type w) := StateT (ULift.{w} Nat) (Except Rejection) α

private def spend : Search (PUnit.{w+1}) := do
  let remaining : ULift.{w} Nat ← get
  match remaining.down with
  | 0 => throw .budget
  | fuel + 1 =>
    set (⟨fuel⟩ : ULift.{w} Nat)
    return ⟨⟩

private structure Mapping (rows n loops l : Nat) where
  rowsMap : Pairs rows n := []
  loopsMap : Pairs loops l := []

private def sameLabel [∀ ins out, DecidableEq (P ins out)] {ins : List (Ty Data)} :
    Label P args (Fin loops) ins t → Label P params (Fin l) ins t → Option (List (Task rows n loops l))
  | .op a, .op b => if a = b then some [] else none
  | .phi, .phi => some []
  | .theta a, .theta b | .eval a, .eval b | .pass a, .pass b => some [.inr (a, b)]
  | _, _ => none

/-- Once an internal row is paired, its ordered dependencies are forced.
Parameters instead terminate the walk at a row in the available bundle.
Only loop keys have to be injective. -/
private def rowTasks [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n l) (leaf : Leaf roles) (available : List (Fin n))
    (i : Fin leaf.rows) (j : Fin n) : Option (List (Task leaf.rows n leaf.loops l)) := do
  if typed : g.sort j = leaf.graph.sort i then
    match leaf.graph.node i with
    | ⟨_, .param _, _⟩ => if j ∈ available then some [] else none
    | ⟨inputs, label, operands⟩ =>
      let target : Node P params (Fin l) g.sort (leaf.graph.sort i) := typed ▸ g.node j
      if arity : target.inputs = inputs then
        let labels ← sameLabel label (arity ▸ target.label)
        return (refIds operands |>.zip (refIds target.args)).map Sum.inl ++ labels
      else none
  else none

private def visit [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n l) (leaf : Leaf roles) (available : List (Fin n)) :
    Nat → List (Task leaf.rows n leaf.loops l) → Mapping leaf.rows n leaf.loops l →
      Search (Option (ULift.{max u v} (Mapping leaf.rows n leaf.loops l)))
  | _, [], pairs => pure (some ⟨pairs⟩)
  | 0, _ :: _, _ => pure none
  | steps + 1, task :: rest, pairs => do
    spend
    match task with
    | .inl (i, j) =>
      match pairs.rowsMap.forward i with
      | some prior =>
        if prior = j then visit g leaf available steps rest pairs else pure none
      | none =>
        let some tasks := rowTasks g leaf available i j | return none
        visit g leaf available steps (tasks ++ rest) { pairs with rowsMap := (i, j) :: pairs.rowsMap }
    | .inr (i, j) =>
      let some (fresh, pairs') := pairs.loopsMap.insert i j | return none
      if fresh then
        let some parents := loopTasks (n := leaf.rows) (n' := n)
          (leaf.graph.forest.parent i) (g.forest.parent j) | return none
        visit g leaf available steps (parents ++ rest) { pairs with loopsMap := pairs' }
      else visit g leaf available steps rest pairs
termination_by structural steps _ _ => steps

private def formStage [DecidableEq Data] (g : Graph P params results n l)
    (leaf : Leaf roles) (pairs : Mapping leaf.rows n leaf.loops l) :
    Option {s : Stage g leaf.inputs leaf.outputs // RegionRoles roles s.region} := do
  if mapped : ∀ i, (pairs.rowsMap.forward i).isSome then
    let row := fun i => (pairs.rowsMap.forward i).get (mapped i)
    if typed : ∀ i, g.sort (row i) = leaf.graph.sort i then
      if linked : ∀ i, (pairs.loopsMap.forward i).isSome then
        let keys := fun i => (pairs.loopsMap.forward i).get (linked i)
        return ⟨⟨leaf.rows, leaf.loops, leaf.graph, leaf.region, fun i => ⟨row i, typed i⟩, keys⟩, leaf.roleMatch⟩
      else none
    else none
  else none

private def projectRefs (available : Tuple (Ref g.sort) before) :
    {outs : List (Ty Data)} → Tuple (Ref g.sort) outs → Option (Tuple (Port before) outs)
  | _, .nil => some .nil
  | _, .cons r rest => do
    let p ← lookup r available
    return .cons p.val (← projectRefs available rest)

private def paramsAt [DecidableEq Data] (graph : Graph P params results n l) :
    {ts : List (Ty Data)} → Tuple (Port params) ts → Option (Tuple (Ref graph.sort) ts)
  | _, .nil => some .nil
  | _, .cons p rest => do
    let refs := (List.finRange n).filterMap fun i => Ref.check graph.sort _ i.val
    let matching := refs.filter fun r => match nodeAt graph r with
      | ⟨_, .param q, _⟩ => @decide (q = p) (RawGraph.Check.portEq q p)
      | _ => false
    let [r] := matching | none
    return .cons r (← paramsAt graph rest)

private def stageRoute [DecidableEq Data] (s : Stage g args outs) (available : Tuple (Ref g.sort) before) :
    Option (Tuple (Port before) args) := do
  let localInputs ← paramsAt s.graph (ports args)
  projectRefs available (localInputs.map fun _ => While.Siblings.push s.addresses)

/-- Search for anchors only for rows the previous walk did not determine.
The continuation can reject a match and request the next alternative. -/
private def matchRows [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)] {α : Type (max u v)}
    (g : Graph P params results n l) (leaf : Leaf roles) (available : Tuple (Ref g.sort) before)
    (accept : (s : Stage g leaf.inputs leaf.outputs) → RegionRoles roles s.region →
      Tuple (Port before) leaf.inputs → Search (Option α)) :
    List (Fin leaf.rows) → Mapping leaf.rows n leaf.loops l → Search (Option α)
  | [], pairs => do
    let some s := formStage g leaf pairs | return none
    let some routing := stageRoute s.val available | return none
    letI := s.val.check (route routing available)
    if s.val.Valid (route routing available) then
      accept s.val s.property routing
    else pure none
  | i :: tail, pairs => do
    if (pairs.rowsMap.forward i).isSome then matchRows g leaf available accept tail pairs
    else
      let steps := 1 + leaf.loops + leaf.rows +
        ((List.finRange leaf.rows).map fun j => (leaf.graph.node j).inputs.length).sum
      let availableRows := refIds available
      let candidates := match leaf.graph.node i with
        | ⟨_, .param _, _⟩ => availableRows
        | _ => List.finRange n
      candidates.findSomeM? fun j => do
        let some next ← visit g leaf availableRows steps [.inl (i, j)] pairs | return none
        matchRows g leaf available accept tail next.down
termination_by structural pending _ => pending

/-- A checked leaf with its original row and loop placement fixed. The
order search may choose when to run it, with these exact input cuts. -/
structure Anchored (g : Graph P params results n l) (roles : Roles P)
    (args outs : List (Ty Data)) where
  stage : Stage g args outs
  inputs : Tuple (Ref g.sort) args
  valid : stage.Valid inputs
  roleMatch : RegionRoles roles stage.region

private inductive Candidate (g : Graph P params results n l) (roles : Roles P) where
  | unplaced : Leaf roles → Candidate g roles
  | anchored {args outs : List (Ty Data)} : Anchored g roles args outs → Candidate g roles

private def propose [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)] {α : Type (max u v)}
    (g : Graph P params results n l) :
    Nat → List (Candidate g roles) → {before : List (Ty Data)} → Tuple (Ref g.sort) before →
    ((p : Plan g before results) → PlanRoles roles p → Search (Option α)) → Search (Option α)
  | _, [], _, available, accept => do
    let some projection := projectRefs available g.roots | return none
    accept (.done projection) trivial
  | 0, _ :: _, _, _, _ => pure none
  | remaining + 1, leaves@(_ :: _), _, available, accept =>
    leaves.zipIdx.findSomeM? fun (candidate, i) => do
      spend
      let extend {args outs : List (Ty Data)} (s : Stage g args outs)
          (law : RegionRoles roles s.region) (routing : Tuple (Port _) args) :=
        propose g remaining (leaves.eraseIdx i) s.output fun tail laws =>
          accept (.step routing s tail) ⟨law, laws⟩
      match candidate with
      | .unplaced leaf =>
        matchRows g leaf available extend (entryPass leaf.region :: List.finRange leaf.rows) {}
      | .anchored leaf =>
        let some routing := projectRefs available leaf.inputs | return none
        extend leaf.stage leaf.roleMatch routing
termination_by structural remaining _ _ _ _ => remaining

structure Found [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n l) (roles : Roles P) (rank : DemandRank n l) : Type (max u v) where
  plan : Plan g params results
  inputs : Tuple (Ref g.sort) params
  gate : {a : Accepted g // a.plan = plan}
  checked : Schedule.check g plan inputs rank = some gate
  roleMatch : PlanRoles roles plan

private def discoverCandidates [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n l) (roles : Roles P) (rank : DemandRank n l)
    (leaves : List (Candidate g roles)) (budget : Nat) : Except Rejection (Found g roles rank) := do
  unless rank.check g do throw .invalidRank
  let some inputs := paramsAt g (ports params) | throw .parameterRows
  let search : Search (Option (Found g roles rank)) := propose g leaves.length leaves inputs fun plan roles => do
    match checked : Schedule.check g plan inputs rank with
    | none => return none
    | some gate => return some ⟨plan, inputs, gate, checked, roles⟩
  let (found, _) ← search.run ⟨budget⟩
  match found with
  | none => throw .noPlan
  | some result => pure result

/-- Use every candidate once. Budget is shared across leaf choices and row
or loop worklist requests, including backtracking. A proposed sequence
must pass the existing schedule checker on the original table. -/
def discover [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n l) (roles : Roles P) (rank : DemandRank n l)
    (leaves : List (Leaf roles)) (budget : Nat) : Except Rejection (Found g roles rank) :=
  discoverCandidates g roles rank (leaves.map Candidate.unplaced) budget

/-- Search only for the order of fixed cuts and the typed projections
that connect them. The budget counts attempted stage choices. -/
def discoverAnchored [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n l) (roles : Roles P) (rank : DemandRank n l)
    (leaves : List (Σ args outs, Anchored g roles args outs))
    (budget : Nat) : Except Rejection (Found g roles rank) :=
  discoverCandidates g roles rank (leaves.map fun ⟨_, _, leaf⟩ => .anchored leaf) budget

end Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic
