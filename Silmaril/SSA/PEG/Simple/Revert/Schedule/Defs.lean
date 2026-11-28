module

public import Silmaril.SSA.PEG.Simple.Revert.While.Siblings.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Defs

/-! # Typed sequential schedules of checked PEG regions -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.Schedule

open RVSDG (Port Tuple)
open While.Region (allPorts nodeEq refEq tupleEq)
open While.Siblings (Addresses push)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results args outs next results' : List (Ty Data)} {n l rows loops : Nat} {t : Ty Data}
variable {g : Graph P params results n l}

/-- A verified region in its own typed parameter and loop contexts. -/
inductive Region : {args outs : List (Ty Data)} → {rows loops : Nat} →
    Graph P args outs rows loops → Type (max u v)
  | closed {args outs : List (Ty Data)} {rows : Nat} {localGraph : Graph P args outs rows 1} {carried} :
    While.Region.Closed.Accepted localGraph carried → Region localGraph
  | nested {args : List (Ty Data)} {t : Ty Data} {rows loops : Nat} {localGraph : Graph P args [t] rows loops} {inner} :
    While.Nested.Region.Accepted localGraph inner → Region localGraph

open While.Nested.Region (Accepted) in
/-- Retain just the nested program's declared return in the output store. -/
def nestedReturn {localGraph : Graph P args [t] rows loops} {inner}
    (a : Accepted localGraph inner) : Stmt P true args [t] :=
  .seq a.revert.body (.project (.cons a.revert.retvar .nil))

def Region.revert {localGraph : Graph P args outs rows loops} :
    Region localGraph → Stmt P true args outs
  | .closed a => a.revert
  | .nested a => nestedReturn a

def Region.runFuel {localGraph : Graph P args outs rows loops}
    (m : Interpretation.{u,v,w} P) (fuel : Nat) (input : Tuple m.Value args) :
    Region localGraph → Option (Tuple m.Value outs)
  | .closed a => a.runFuel m fuel input
  | .nested a => (a.runFuel m fuel fuel input).map fun value => .cons value .nil

def Region.Laws {localGraph : Graph P args outs rows loops}
    (m : Interpretation.{u,v,w} P) : Region localGraph → Prop
  | .closed a => a.Laws m
  | .nested a => ∀ b : Bool, m.run a.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩

/-- Record all first exits required by the local region. The nested case
samples the child separately at every continuing outer activation. -/
def Region.Exits {localGraph : Graph P args outs rows loops}
    (m : Interpretation.{u,v,w} P) (values : localGraph.Valuation m)
    (i : Index loops) : Region localGraph → Prop
  | .closed a => ∃ k, a.FirstExit m values i k
  | .nested a => ∃ k, a.FirstExits m values i k

/-- The converse requires the existing region-specific slice premises.
Nested totality is relative to the realized stores of this valuation. -/
def Region.Slices {localGraph : Graph P args outs rows loops}
    (m : Interpretation.{u,v,w} P) (values : localGraph.Valuation m) : Region localGraph → Prop
  | .closed a => a.Total m
  | .nested a => a.DefinedSlices m values

abbrev nodeAt (g : Graph P params results n l) (r : Ref g.sort t) : Node P params (Fin l) g.sort t :=
  r.typed ▸ g.node r.id

/-- A local parameter is an input cut. All other rows retain their
constructors, ordered operands and mapped loop keys. -/
def expected {localGraph : Graph P args outs rows loops}
    (keys : Fin loops → Fin l) (addresses : Addresses localGraph.sort g.sort) :
    {t : Ty Data} → Node P args (Fin loops) localGraph.sort t →
      Port args t ⊕ Node P params (Fin l) g.sort t
  | _, ⟨_, .param p, _⟩ => .inl p
  | _, ⟨_, .op op, refs⟩ => .inr (.ofLabel (.op op) (refs.map fun _ => push addresses))
  | _, ⟨_, .phi, refs⟩ => .inr (.ofLabel .phi (refs.map fun _ => push addresses))
  | _, ⟨_, .theta key, refs⟩ => .inr (.ofLabel (.theta (keys key)) (refs.map fun _ => push addresses))
  | _, ⟨_, .pass key, refs⟩ => .inr (.ofLabel (.pass (keys key)) (refs.map fun _ => push addresses))
  | _, ⟨_, .eval key, refs⟩ => .inr (.ofLabel (.eval (keys key)) (refs.map fun _ => push addresses))

/-- One local accepted region and its proposed embedding into the original
graph. Row aliases are allowed, including aliases at input cuts. -/
structure Stage (g : Graph P params results n l) (args outs : List (Ty Data)) where
  rows : Nat
  loops : Nat
  graph : Graph P args outs rows loops
  region : Region graph
  addresses : Addresses graph.sort g.sort
  keys : Fin loops → Fin l

def Stage.output (s : Stage g args outs) : Tuple (Ref g.sort) outs :=
  s.graph.roots.map fun _ => push s.addresses

def Stage.Matches (s : Stage g args outs) (inputs : Tuple (Ref g.sort) args) (i : Fin s.rows) : Prop :=
  match expected s.keys s.addresses (s.graph.node i) with
  | .inl port => s.addresses i = inputs.get port
  | .inr row => nodeAt g (s.addresses i) = row

structure Stage.Valid (s : Stage g args outs) (inputs : Tuple (Ref g.sort) args) : Prop where
  injective : Function.Injective s.keys
  scopes : ∀ key, g.forest.parent (s.keys key) = (s.graph.forest.parent key).map s.keys
  rows : ∀ i, s.Matches inputs i

def Stage.check [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (s : Stage g args outs) (inputs : Tuple (Ref g.sort) args) : Decidable (s.Valid inputs) := by
  letI (i : Fin s.rows) : Decidable (s.Matches inputs i) := by
    unfold Matches
    split
    · exact refEq _ _
    · exact nodeEq _ _
  exact decidable_of_iff
    ((∀ i j, s.keys i = s.keys j → i = j) ∧
      (∀ key, g.forest.parent (s.keys key) = (s.graph.forest.parent key).map s.keys) ∧
      (∀ i, s.Matches inputs i))
    ⟨fun ⟨keys, scopes, rows⟩ => ⟨fun _ _ => keys _ _, scopes, rows⟩, fun h => ⟨fun _ _ eq => h.injective eq, h.scopes, h.rows⟩⟩

/-- A cut is supplied by a typed store at every index. Closed sequential
boundaries establish this invariant before entering the next stage. -/
def Realizes (m : Interpretation.{u,v,w} P) (values : g.Valuation m) (refs : Tuple (Ref g.sort) args) (input : Tuple m.Value args) : Prop :=
  ∀ i t (p : Port args t), Rules.readRef values (refs.get p) i = some (input.get p)

/-- Fix unmapped coordinates at the enclosing index and replace precisely
the mapped coordinates with those of the local activation. -/
noncomputable def embedIndex {k : Nat} (keys : Fin k → Fin l) (base : Index l) (i : Index k) : Index l :=
  fun j => if h : ∃ k, keys k = j then i (Classical.choose h) else base j

noncomputable def Stage.pull (s : Stage g args outs) (m : Interpretation.{u,v,w} P) (values : g.Valuation m) (base : Index l) : s.graph.Valuation m :=
  fun q => Rules.readRef values (s.addresses q.1) (embedIndex s.keys base q.2)

def Stage.Exits (s : Stage g args outs) (m : Interpretation.{u,v,w} P)
    (values : g.Valuation m) (base : Index l) : Prop :=
  s.region.Exits m (s.pull m values base) (fun key => base (s.keys key))

def route {F : Ty Data → Type w} (slots : Tuple (Port args) outs) (store : Tuple F args) : Tuple F outs :=
  slots.map fun _ p => store.get p

/-- Any finite sequence of stages. Each boundary can reorder, discard or
duplicate ports of the preceding store, including inputs retained by it. -/
inductive Plan (g : Graph P params results n l) : List (Ty Data) → List (Ty Data) → Type (max u v)
  | done {args outs : List (Ty Data)} (slots : Tuple (Port args) outs) : Plan g args outs
  | step {args outs next results' : List (Ty Data)} (slots : Tuple (Port args) next) (stage : Stage g next outs)
      (tail : Plan g outs results') : Plan g args results'

def Plan.Valid : {args outs : List (Ty Data)} →
    Plan g args outs → Tuple (Ref g.sort) args → Tuple (Ref g.sort) outs → Prop
  | _, _, .done slots, input, output => route slots input = output
  | _, _, .step slots stage tail, input, output => stage.Valid (route slots input) ∧ tail.Valid stage.output output

def Plan.check [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)] :
    {args outs : List (Ty Data)} → (p : Plan g args outs) →
      (input : Tuple (Ref g.sort) args) → (output : Tuple (Ref g.sort) outs) →
        Decidable (p.Valid input output)
  | _, _, .done slots, input, output => tupleEq (route slots input) output
  | _, _, .step slots stage tail, input, output =>
    letI := stage.check (route slots input)
    letI := tail.check stage.output output
    inferInstanceAs (Decidable (_ ∧ _))

def Plan.revert : {args outs : List (Ty Data)} → Plan g args outs → Stmt P true args outs
  | _, _, .done slots => .project slots
  | _, _, .step slots stage tail => .seq (.project slots) (.seq stage.region.revert tail.revert)

def Plan.runFuel (m : Interpretation.{u,v,w} P) (fuel : Nat) :
    {args outs : List (Ty Data)} → Plan g args outs → Tuple m.Value args → Option (Tuple m.Value outs)
  | _, _, .done slots, input => some (route slots input)
  | _, _, .step slots stage tail, input =>
    (stage.region.runFuel m fuel (route slots input)).bind (tail.runFuel m fuel)

def Plan.Laws (m : Interpretation.{u,v,w} P) :
    {args outs : List (Ty Data)} → Plan g args outs → Prop
  | _, _, .done _ => True
  | _, _, .step _ stage tail => stage.region.Laws m ∧ tail.Laws m

/-- The first exits and intermediate stores observed at one original
index. The next stage consumes the same ordered ports as the emitted code. -/
def Plan.Observations (m : Interpretation.{u,v,w} P) (values : g.Valuation m) (base : Index l) :
    {args outs : List (Ty Data)} → Plan g args outs → Tuple (Ref g.sort) outs → Tuple m.Value outs → Prop
  | _, _, .done _, refs, result =>
    ∀ t (p : Port _ t), Rules.readRef values (refs.get p) base = some (result.get p)
  | _, _, .step _ stage tail, refs, result =>
    stage.Exits m values base ∧
      ∃ mid : Tuple m.Value _, (∀ t (p : Port _ t), Rules.readRef values (stage.output.get p) base = some (mid.get p)) ∧
        tail.Observations m values base refs result

def Plan.Slices (m : Interpretation.{u,v,w} P) (values : g.Valuation m) (base : Index l) :
    {args outs : List (Ty Data)} → Plan g args outs → Prop
  | _, _, .done _ => True
  | _, _, .step _ stage tail =>
    stage.region.Slices m (stage.pull m values base) ∧ tail.Slices m values base

def ParameterRows (g : Graph P params results n l) (inputs : Tuple (Ref g.sort) params) : Prop :=
  ∀ t (p : Port params t), nodeAt g (inputs.get p) = .ofLabel (.param p) .nil

structure Accepted (g : Graph P params results n l) where
  plan : Plan g params results
  inputs : Tuple (Ref g.sort) params
  parameters : ParameterRows g inputs
  valid : plan.Valid inputs g.roots
  rank : DemandRank n l
  ranked : rank.check g = true

def check [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n l) (plan : Plan g params results)
    (inputs : Tuple (Ref g.sort) params) (rank : DemandRank n l) : Option {a : Accepted g // a.plan = plan} :=
  letI : Decidable (ParameterRows g inputs) := allPorts params _ (fun _ _ => nodeEq _ _)
  letI := plan.check inputs g.roots
  if h : ParameterRows g inputs ∧ plan.Valid inputs g.roots ∧ rank.check g = true then
    some ⟨⟨plan, inputs, h.1, h.2.1, rank, h.2.2⟩, rfl⟩
  else none

end Silmaril.SSA.PEG.Simple.Revert.Schedule
