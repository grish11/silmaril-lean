module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Defs
public import Silmaril.SSA.PEG.Rules.Defs

/-! # Two checked parentless loops with a typed handoff -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Siblings

open RVSDG (Port Tuple)
open Simple.Revert.While.Region

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params intermediate args results carried₁ carried₂ ts : List (Ty Data)}
variable {n n₁ n₂ : Nat} {t : Ty Data}
variable {sort : Fin n → Ty Data} {sourceSort : Fin n₁ → Ty Data}
variable {g : Graph P params results n 2}
variable {left : Graph P params intermediate n₁ 1} {right : Graph P args results n₂ 1}

/-- Local rows map to typed original references. Two input rows can alias
one boundary value, so the correspondence need not be injective. -/
abbrev Addresses (sourceSort : Fin n₁ → Ty Data) (sort : Fin n → Ty Data) :=
  (i : Fin n₁) → Ref sort (sourceSort i)

def push (addresses : Addresses sourceSort sort) (ref : Ref sourceSort t) : Ref sort t :=
  ⟨(addresses ref.id).id, (addresses ref.id).typed.trans ref.typed⟩

abbrev nodeAt (g : Graph P params results n 2) (r : Ref g.sort t) : Node P params (Fin 2) g.sort t :=
  r.typed ▸ g.node r.id

/-- A stage parameter is a cut leaf. Every internal row is checked
against the original label, loop key, and ordered operands. -/
def expected (key : Fin 2) (addresses : Addresses sourceSort sort) :
    {t : Ty Data} → Node P args (Fin 1) sourceSort t → Option (Port args t ⊕ Node P params (Fin 2) sort t)
  | _, ⟨_, .param p, _⟩ => some (.inl p)
  | _, ⟨_, .op op, refs⟩ => some (.inr (.ofLabel (.op op) (refs.map fun _ => push addresses)))
  | _, ⟨_, .theta _, refs⟩ => some (.inr (.ofLabel (.theta key) (refs.map fun _ => push addresses)))
  | _, ⟨_, .pass _, refs⟩ => some (.inr (.ofLabel (.pass key) (refs.map fun _ => push addresses)))
  | _, ⟨_, .eval _, refs⟩ => some (.inr (.ofLabel (.eval key) (refs.map fun _ => push addresses)))
  | _, ⟨_, .phi, _⟩ => none

def Matches (g : Graph P params results n 2) (stage : Graph P args ts n₁ 1)
    (key : Fin 2) (addresses : Addresses stage.sort g.sort) (inputs : Tuple (Ref g.sort) args)
    (i : Fin n₁) : Prop :=
  match expected (params := params) key addresses (stage.node i) with
  | some (.inl p) => addresses i = inputs.get p
  | some (.inr row) => nodeAt g (addresses i) = row
  | none => False

def matchesDec [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n 2) (stage : Graph P args ts n₁ 1)
    (key : Fin 2) (addresses : Addresses stage.sort g.sort) (inputs : Tuple (Ref g.sort) args)
    (i : Fin n₁) : Decidable (Matches g stage key addresses inputs i) := by
  unfold Matches
  split
  · exact refEq _ _
  · exact nodeEq _ _
  · exact isFalse id

/-- The first output bundle includes any original inputs that the second
stage needs. The boundary can reorder, discard or duplicate its ports. -/
structure Layout (g : Graph P params results n 2)
    (left : Graph P params intermediate n₁ 1) (right : Graph P args results n₂ 1) where
  first : Addresses left.sort g.sort
  second : Addresses right.sort g.sort
  inputs : Tuple (Ref g.sort) params
  route : Tuple (Port intermediate) args

variable (d : Layout g left right)

def Layout.firstRoots : Tuple (Ref g.sort) intermediate :=
  left.roots.map fun _ => push d.first

def Layout.secondRoots : Tuple (Ref g.sort) results :=
  right.roots.map fun _ => push d.second

def Layout.rightInputs : Tuple (Ref g.sort) args :=
  d.route.map fun _ p => d.firstRoots.get p

def Layout.handoff (m : Interpretation.{u,v,w} P) (mid : Tuple m.Value intermediate) : Tuple m.Value args :=
  d.route.map fun _ p => mid.get p

structure Boundary (d : Layout g left right) : Prop where
  firstParentless : g.forest.parent 0 = none
  secondParentless : g.forest.parent 1 = none
  inputs : ∀ t (p : Port params t), nodeAt g (d.inputs.get p) = .ofLabel (.param p) .nil
  first : ∀ i, Matches g left 0 d.first d.inputs i
  second : ∀ i, Matches g right 1 d.second d.rightInputs i
  output : d.secondRoots = g.roots

structure Accepted (g : Graph P params results n 2)
    (first : Closed.Accepted left carried₁) (second : Closed.Accepted right carried₂) where
  layout : Layout g left right
  boundary : Boundary layout
  rank : DemandRank n 2
  ranked : rank.check g = true

/-- Check the actual original table, including the provenance of every
second-stage input row. Only the boundary projection connects the stages. -/
def check [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P params results n 2)
    (first : Closed.Accepted left carried₁) (second : Closed.Accepted right carried₂)
    (d : Layout g left right) (rank : DemandRank n 2) : Option (Accepted g first second) :=
  letI : Decidable (∀ t (p : Port params t), nodeAt g (d.inputs.get p) = .ofLabel (.param p) .nil) :=
    allPorts params _ (fun _ _ => nodeEq _ _)
  letI : ∀ i, Decidable (Matches g left 0 d.first d.inputs i) :=
    matchesDec g left 0 d.first d.inputs
  letI : ∀ i, Decidable (Matches g right 1 d.second d.rightInputs i) :=
    matchesDec g right 1 d.second d.rightInputs
  letI := tupleEq d.secondRoots g.roots
  if h : g.forest.parent 0 = none ∧ g.forest.parent 1 = none ∧
      (∀ t (p : Port params t), nodeAt g (d.inputs.get p) = .ofLabel (.param p) .nil) ∧
      (∀ i, Matches g left 0 d.first d.inputs i) ∧
      (∀ i, Matches g right 1 d.second d.rightInputs i) ∧ d.secondRoots = g.roots ∧
      rank.check g = true then
    let ⟨parent₁, parent₂, inputs, first, second, output, ranked⟩ := h
    some ⟨d, ⟨parent₁, parent₂, inputs, first, second, output⟩, rank, ranked⟩
  else none

variable {first : Closed.Accepted left carried₁} {second : Closed.Accepted right carried₂}
variable (a : Accepted g first second)

/-- Each while has its own typed local store. Only the projected boundary
slots enter the second program's input context. -/
def Accepted.revert : Stmt P true params results :=
  .seq first.revert (.seq (.project a.layout.route) second.revert)

def Accepted.runFuel (m : Interpretation.{u,v,w} P) (fuel₁ fuel₂ : Nat)
    (env : Tuple m.Value params) : Option (Tuple m.Value results) :=
  (first.runFuel m fuel₁ env).bind (fun mid => second.runFuel m fuel₂ (a.layout.handoff m mid))

def observeRefs (m : Interpretation.{u,v,w} P) (g : Graph P params results n 2)
    (values : g.Valuation m) (idx : Index 2) (refs : Tuple (Ref g.sort) ts) :
    Tuple (fun t => Option (m.Value t)) ts :=
  refs.map fun _ r => Rules.readRef values r idx

/-- Both first-pass counts and the ordered observations at the original
index, with an explicit intermediate tuple. -/
structure Accepted.Observations (m : Interpretation.{u,v,w} P) (values : g.Valuation m)
    (idx : Index 2) (mid : Tuple m.Value intermediate) (output : Tuple m.Value results) : Prop where
  firstExit : ∃ k, Rules.readRef values (push a.layout.first first.descriptor.pass) idx = some ⟨k⟩
  secondExit : ∃ k, Rules.readRef values (push a.layout.second second.descriptor.pass) idx = some ⟨k⟩
  first : observeRefs m g values idx a.layout.firstRoots = mid.map (fun _ => some)
  second : g.observe m values idx = output.map (fun _ => some)

end Silmaril.SSA.PEG.Simple.Revert.While.Siblings
