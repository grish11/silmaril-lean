module

public import Silmaril.Semantics.ITree.Trace.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod

/-! Finite-state weak trace comparison with Boolean replies. -/

@[expose] public section

namespace Silmaril.Elgot.ITree.Finite

universe u

/-- Requests share the same two-element reply type, and their keys can
record both the opcode and a typed argument. -/
inductive Event (Q : Type) : Type → Type where
  | ask (key : Q) : Event Q Bool

inductive Head (Q : Type) (R S : Type u) where
  | stop
  | result (value : R)
  | request (key : Q) (next : Bool → S)

abbrev Step (Q : Type) (R S : Type u) := Head Q R S ⊕ S

variable {Q : Type} {R S : Type u}

/-- The finite tables implement each transition as a weak Elgot body. -/
def transition (step : S → Step Q R S) (state : S) : Tree (Event Q) (R ⊕ S) :=
  match step state with
  | .inr next => ret (.inr next)
  | .inl .stop => diverge
  | .inl (.result value) => ret (.inl value)
  | .inl (.request key next) => vis (.ask key) (fun reply => ret (.inr (next reply)))

noncomputable def evaluate (step : S → Step Q R S) (state : S) : Tree (Event Q) R :=
  iter (transition step) state

def Head.render (run : S → Tree (Event Q) R) :
    Head Q R S → Part (Visible (Event Q) R (Tree (Event Q) R))
  | .stop => Part.none
  | .result value => Part.some (.ret value)
  | .request key next => Part.some (.vis (.ask key) (run ∘ next))

variable {R S T : Type u} [DecidableEq S]

/-- Follow silent successors until reaching a head or revisiting a state. -/
def headFrom (step : S → Step Q R S) (remaining : Finset S) (state : S) : Head Q R S :=
  if _fresh : state ∈ remaining then
    match step state with
    | .inl head => head
    | .inr next => headFrom step (remaining.erase state) next
  else .stop
termination_by remaining.card
decreasing_by exact Finset.card_erase_lt_of_mem _fresh

/-- Remove locally failing pairs until the candidate simulation is stable. -/
def prune (keep : Finset S → S → Bool) (candidates : Finset S) : Finset S :=
  let next := candidates.filter (fun s => keep candidates s = true)
  if _same : next = candidates then candidates else prune keep next
termination_by candidates.card
decreasing_by
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, _same⟩)

variable [DecidableEq T] [DecidableEq Q] [DecidableEq R]

def compatible (pairs : Finset (S × T)) : Head Q R S → Head Q R T → Bool
  | .stop, _ => true
  | .result left, .result right => decide (left = right)
  | .request left nextL, .request right nextR =>
    decide (left = right) && decide ((nextL false, nextR false) ∈ pairs) &&
      decide ((nextL true, nextR true) ∈ pairs)
  | _, _ => false

/-- Compute the largest finite simulation of the normalized heads. -/
def compare (statesL : Finset S) (statesR : Finset T)
    (left : S → Step Q R S) (right : T → Step Q R T) (startL : S) (startR : T) : Bool :=
  decide ((startL, startR) ∈ prune
    (fun pairs (l, r) => compatible pairs (headFrom left statesL l) (headFrom right statesR r))
    (statesL ×ˢ statesR))

end Silmaril.Elgot.ITree.Finite
