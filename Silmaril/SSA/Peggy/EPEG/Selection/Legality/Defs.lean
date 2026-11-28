module

public import Silmaril.SSA.PEG.Scope
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Rank.Defs

/-! # Cycle constraints on the selected PEG
The reachability variables of §8.3 stop at θ vertices. The repaired
certificate instead exempts just θ feedback edges from a decreasing
rank on the materialized selection. -/

@[expose] public section

namespace Silmaril.SSA.Peggy.EPEG.Selection

open PEG
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}

/-- The three reachability clauses printed in §8.3. Here `chosen` is the
node assignment Bᵢ and `reaches` is Bᵢⱼ. Children are the actual wired
children of the candidate. On a materialized selection all rows are
chosen. The root and class constraints are separate. -/
structure PrintedCycles (g : Graph P params results n l)
    (chosen : Fin n → Bool) (reaches : Fin n → Fin n → Bool) : Prop where
  immediate : ∀ i j kind, chosen i = true → (g.node i).label.thetaLoop = none →
    g.Edge i kind j → reaches i j = true
  propagate : ∀ i j k kind, reaches i j = true → chosen j = true →
    (g.node j).label.thetaLoop = none → g.Edge j kind k → reaches i k = true
  irreflexive : ∀ i, (g.node i).label.thetaLoop = none → reaches i i = false

def SelectedNonThetaEdge (g : Graph P params results n l) (chosen : Fin n → Bool)
    (i : Fin n) (kind : EdgeKind (Fin l)) (j : Fin n) : Prop :=
  chosen i = true ∧ (g.node i).label.thetaLoop = none ∧ g.Edge i kind j

/-- A rank witness for Definition 5.1(1) on the selected edges. Initializer,
ordinary, index and sample edges all participate in the check. -/
structure FeedbackRank (g : Graph P params results n l) where
  rank : Fin n → Nat
  decreases : ∀ i (slot : Fin (g.node i).inputs.length),
    ¬((g.node i).label.kind slot).IsFeedback → rank ((g.node i).arg slot).id < rank i

def FeedbackRank.check (g : Graph P params results n l) (rank : Fin n → Nat) :
    Option (FeedbackRank g) :=
  if ok : ∀ i (slot : Fin (g.node i).inputs.length),
      ¬((g.node i).label.kind slot).IsFeedback → rank ((g.node i).arg slot).id < rank i then
    some ⟨rank, ok⟩
  else none

def nonfeedbackTargets (g : Graph P params results n l) (i : Fin n) : List (Fin n) :=
  let row := g.node i
  (List.finRange row.inputs.length).filterMap fun slot =>
    if (row.label.kind slot).IsFeedback then none else some (row.arg slot).id

/-- Infer sink ranks in at most one round per materialized row, then
independently validate the resulting witness against every ordered slot. -/
def FeedbackRank.infer (g : Graph P params results n l) : Option (FeedbackRank g) :=
  let ranks := Rank.rounds (nonfeedbackTargets g) n
  check g fun i => (ranks.get i).getD 0

end Silmaril.SSA.Peggy.EPEG.Selection
