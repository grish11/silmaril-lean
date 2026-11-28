module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.MixedRows.Defs

/-! # Recover the mixed flat case from its numbered γ -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Reverse

open Isotope.LambdaSSA (Region)
open OrderedRuntime.Structured (Threaded)
open PureRow (Segment Output)
open NestedTheta.ExplicitRuntime.PurePrefix (EntryChecked)
open MixedRows (Row readScope)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A P B C : τ}

abbrev Graph (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A P C : τ) :=
  NestedTheta.Graph (Op (τ := τ) Φ ε) (Threaded (Input A)) [] [Output P C] (Output P C)

def readArms : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    (kind : NestedTheta.Kind (Op (τ := τ) Φ ε) ins outs) →
    {sigs : Fin kind.arity → List (Ports (OrderedRuntime.Structured.Ty τ))} →
    ((j : Fin kind.arity) → NestedTheta.Term (Op (τ := τ) Φ ε) kind.entry [] (sigs j) kind.exit) →
    Option (List (Row τ Φ ε) × List (Row τ Φ ε))
  | _, _, .base (.gamma 0), _, children => do
    return (← readScope (children (0 : Fin 2)), ← readScope (children (1 : Fin 2)))
  | _, _, _, _, _ => none

def read (g : Graph Φ ε A P C) : Option (List (Row τ Φ ε) × List (Row τ Φ ε)) :=
  match g.toTerm with
  | .bind node children (.ret _) => readArms node.kind children

section Decode

variable [DecidableEq τ]

-- The first ordered result sort is internal to the arm.
def decodeSegment (value first last : Row τ Φ ε) : Option (Σ B, Segment Φ ε A P B C) := do
  let .ordered (.call (B := B) first) := first | none
  let .ordered (.call last) := last | none
  let ⟨value, bottom⟩ ← MixedRows.value A P value
  let first ← MixedRows.instruction A B first.op
  let last ← MixedRows.instruction A C last.op
  return ⟨B, ⟨value, bottom, first, last⟩⟩

def decodeLeft : List (Row τ Φ ε) → Option (Σ B, Segment Φ ε A P B C × Bool)
  | [value@(.value ..), first, last] => (decodeSegment value first last).map fun ⟨B, s⟩ => ⟨B, s, true⟩
  | [first, value@(.value ..), last] => (decodeSegment value first last).map fun ⟨B, s⟩ => ⟨B, s, false⟩
  | _ => none

def decodeRight : List (Row τ Φ ε) → Option (Σ B, Segment Φ ε A P B C)
  | [value, first, last] => decodeSegment value first last
  | _ => none

def decode (left right : List (Row τ Φ ε)) : Option (Σ B, Branch Φ ε A P B C × Bool) := do
  let ⟨leftSort, l, pureFirst⟩ ← decodeLeft left
  let ⟨rightSort, r⟩ ← decodeRight right
  if same : rightSort = leftSort then
    return ⟨leftSort, ⟨l, same ▸ r⟩, pureFirst⟩
  else none

/-- Recover the typed labels and the left row order from the child tables.
Wiring is checked against the full input graph after this step. -/
def candidate (g : Graph Φ ε A P C) : Option (Σ B, Branch Φ ε A P B C × Bool) := do
  let (left, right) ← read g
  decode left right

end Decode

/-- The recovered flat case and the exact numbered wiring certificate. -/
structure Fibre (g : Graph Φ ε A P C) where
  middle : τ
  branch : Branch Φ ε A P middle C
  pureFirst : Bool
  wiring : branch.compile pureFirst = g

def Fibre.region {g : Graph Φ ε A P C} (f : Fibre g) : Region Φ := f.branch.region

theorem Fibre.typing {g : Graph Φ ε A P C} (f : Fibre g) :
    Region.HasType [Choice A] f.region [Silmaril.product P C] := f.branch.typing

def Fibre.checked {g : Graph Φ ε A P C} (f : Fibre g) :
    EntryChecked (a := inputData A) (b := resultsData P C) g.toTerm :=
  f.wiring ▸ f.branch.compileChecked f.pureFirst

variable [DecidableEq τ] [DecidableEq Φ]

def certify (g : Graph Φ ε A P C) (c : Σ B, Branch Φ ε A P B C × Bool) : Option (Fibre g) :=
  letI := MixedRows.decideGraph (c.2.1.compile c.2.2) g
  if same : c.2.1.compile c.2.2 = g then some ⟨c.1, c.2.1, c.2.2, same⟩ else none

/-- Graph-only recovery at either emitted left-child numbering. -/
def recover (g : Graph Φ ε A P C) : Option (Fibre g) :=
  (candidate g).bind (certify g)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Reverse
