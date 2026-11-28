module

public import Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Defs
public import Silmaril.SSA.PEG.Projection.Defs

/-! # Build checked schedule leaves from typed cuts of the original PEG -/

public section

namespace Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Cuts

open RVSDG (Tuple)
open While.Region (lookup)
open PEG.Reindex.Automatic (refIds)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat} {g : Graph P params results n l}

/-- A candidate scope interface. Input references are the exact cut
leaves; output references are the values exported in typed store order. -/
structure Boundary (g : Graph P params results n l) where
  args : List (Ty Data)
  outs : List (Ty Data)
  inputs : Tuple (Ref g.sort) args
  outputs : Tuple (Ref g.sort) outs

inductive Unsupported where
  | repeatedInput
  | coverage
  | loopShape
  | leafCheck
  | placement
  deriving DecidableEq, Repr

inductive Failure where
  | unsupported (candidate : Nat) (reason : Unsupported)
  | schedule (reason : Rejection)
  deriving DecidableEq, Repr

/-- Each successful cut is a checked stage with the exact supplied input
and output references in the original graph. -/
structure CheckedCut (b : Boundary g) (roles : Roles P) where
  leaf : Anchored g roles b.args b.outs
  inputs_eq : leaf.inputs = b.inputs
  outputs_eq : leaf.stage.output = b.outputs

/-- A fresh non-cut row adds its ordered operands, including feedback.
Cut rows are kept but act as opaque leaves. -/
private def visit (g : Graph P params results n l) (cuts : List (Fin n)) :
    Nat → List (Fin n) → List (Fin n) → Option (List (Fin n))
  | _, [], seen => some seen
  | 0, _ :: _, _ => none
  | fuel + 1, row :: pending, seen =>
    if row ∈ seen then visit g cuts fuel pending seen
    else
      let deps := if row ∈ cuts then [] else refIds (g.node row).args
      visit g cuts fuel (deps ++ pending) (row :: seen)
termination_by structural fuel _ _ => fuel

/-- Compute the dependency closure in row order, treating the cut rows as leaves. -/
def dependencyRows (g : Graph P params results n l) (cuts seeds : List (Fin n)) :
    Option (Projection.Rows n) := do
  let all := List.finRange n
  let edges := (all.map fun i => (g.node i).inputs.length).sum
  let seen ← visit g cuts (seeds.length + edges) seeds []
  return all.filter fun i => i ∈ seen

private def supported (forest : LoopForest l) (outputs : Nat) : List (Fin l) → Bool
  | [key] => (forest.parent key).isNone
  | [a, b] => outputs == 1 &&
    (((forest.parent a).isNone && forest.parent b == some a) ||
      ((forest.parent b).isNone && forest.parent a == some b))
  | _ => false

private def localLabel {args ins : List (Ty Data)} {t : Ty Data} (keys : Projection.Rows l) :
    Label P params (Fin l) ins t → Option (Label P args (Fin keys.length) ins t)
  | .param _ => none
  | .op op => some (.op op)
  | .phi => some .phi
  | .theta key => (Projection.findRow keys key).map fun mapped => .theta mapped.val
  | .eval key => (Projection.findRow keys key).map fun mapped => .eval mapped.val
  | .pass key => (Projection.findRow keys key).map fun mapped => .pass mapped.val

private def localNode (g : Graph P params results n l) (b : Boundary g)
    (rows : Projection.Rows n) (keys : Projection.Rows l) (i : Fin rows.length) :
    Option (Node P b.args (Fin keys.length) (g.sort ∘ rows.embed) (g.sort (rows.embed i))) := do
  let old := rows.embed i
  if let some input := lookup (Ref.ofId g.sort old) b.inputs then
    return .ofLabel (.param input.val) .nil
  else
    let row := g.node old
    let label ← localLabel keys row.label
    let some refs := Projection.Wires.check rows row.args | none
    return .ofLabel label refs.refs

private def localRank (rows : Projection.Rows n) (keys : Projection.Rows l)
    (rank : DemandRank n l) : DemandRank rows.length keys.length :=
  rank.filterMap fun
    | .phase heights => some (.phase (heights ∘ rows.embed))
    | .counter key => (Projection.findRow keys key).map fun mapped => .counter mapped.val

private def recognize [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    {args : List (Ty Data)} {rows : Nat} (roles : Roles P) :
    {outs : List (Ty Data)} → {loops : Nat} → (graph : Graph P args outs rows loops) →
    DemandRank rows loops → Option {r : Region graph // RegionRoles roles r}
  | _, 1, graph, _ => do
    match h : roles with
    | .counted ops =>
      let leaf ← While.Region.Closed.Automatic.extract graph ops
      return ⟨.closed leaf.certificate, by
        rw [h]
        exact ⟨leaf.zero, leaf.tick, leaf.negate⟩⟩
    | .nestedOnly _ => none
  | [_], 2, graph, rank => do
    let leaf ← While.Nested.Region.Automatic.extract graph rank roles.negate
    return ⟨.nested leaf.certificate, leaf.negate_eq⟩
  | _, _, _, _ => none

/-- Build a local graph from the exported roots, stopping at the cut
leaves. Retain all loop-labelled rows for the selected keys before
closing dependencies again, including any unread child eval port. -/
def synthesize [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n l) (roles : Roles P) (rank : DemandRank n l) (b : Boundary g) :
    Except Unsupported (CheckedCut b roles) := do
  let cuts := refIds b.inputs
  unless decide cuts.Nodup do throw .repeatedInput
  let seeds := refIds b.outputs ++ cuts
  let some demanded := dependencyRows g cuts seeds | throw .coverage
  let keys : Projection.Rows l := (List.finRange l).filter fun key =>
    demanded.any fun i => i ∉ cuts && (g.node i).label.loop == some key
  unless supported g.forest b.outs.length keys do throw .loopShape
  let loopRows := (List.finRange n).filter fun i =>
    ((g.node i).label.loop).any fun key => key ∈ keys
  let some rows := dependencyRows g cuts (seeds ++ loopRows) | throw .coverage
  let some exports := Projection.Wires.check rows b.outputs | throw .coverage
  let nodes := localNode g b rows keys
  if covered : ∀ i, (nodes i).isSome then
    let graph : Graph P b.args b.outs rows.length keys.length :=
      ⟨⟨fun i => (g.forest.parent (keys.embed i)).bind fun p =>
        (Projection.findRow keys p).map Subtype.val⟩,
        g.sort ∘ rows.embed, fun i => (nodes i).get (covered i), exports.refs⟩
    let some region := recognize roles graph (localRank rows keys rank) | throw .leafCheck
    let stage : Stage g b.args b.outs :=
      ⟨_, _, graph, region.val, fun i => Ref.ofId g.sort (rows.embed i), keys.embed⟩
    letI := stage.check b.inputs
    if valid : stage.Valid b.inputs then
      return ⟨⟨stage, b.inputs, valid, region.property⟩, rfl, exports.agrees⟩
    else throw .placement
  else throw .coverage

/-- Infer the checked leaves and search their order. Unordered cuts fix
only interfaces and placement, and the original checker still admits the
complete sequence with its final projection. -/
def discover [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n l) (roles : Roles P) (rank : DemandRank n l)
    (boundaries : List (Boundary g)) (budget : Nat) : Except Failure (Found g roles rank) := do
  unless rank.check g do throw (.schedule .invalidRank)
  let stages ← boundaries.zipIdx.mapM fun (b, i) =>
    match synthesize g roles rank b with
    | .error reason => .error (.unsupported i reason)
    | .ok result => .ok ⟨b.args, b.outs, result.leaf⟩
  (discoverAnchored g roles rank stages budget).mapError Failure.schedule

end Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Cuts
