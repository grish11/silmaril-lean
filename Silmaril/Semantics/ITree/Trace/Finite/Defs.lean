module

public import Silmaril.Semantics.ITree.Trace.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Pi

/-! Finite-state weak trace comparison with finite request-indexed replies. -/

@[expose] public section

namespace Silmaril.Elgot.ITree.Finite

universe u

/-- A request key determines the reply type. The key can include the opcode and its typed argument. -/
inductive Event (Q : Type) (Reply : Q → Type := fun _ => Bool) : Type → Type where
  | ask (key : Q) : Event Q Reply (Reply key)

inductive Head (Q : Type) (R S : Type u) (Reply : Q → Type := fun _ => Bool) where
  | stop
  | result (value : R)
  | request (key : Q) (next : Reply key → S)

abbrev Step (Q : Type) (R S : Type u) (Reply : Q → Type := fun _ => Bool) := Head Q R S Reply ⊕ S

variable {Q : Type} {Reply : Q → Type} {R S : Type u}

/-- The finite tables implement each transition as a weak Elgot body. -/
def transition (step : S → Step Q R S Reply) (state : S) : Tree (Event Q Reply) (R ⊕ S) :=
  match step state with
  | .inr next => ret (.inr next)
  | .inl .stop => diverge
  | .inl (.result value) => ret (.inl value)
  | .inl (.request key next) => vis (.ask key) (fun reply => ret (.inr (next reply)))

noncomputable def evaluate (step : S → Step Q R S Reply) (state : S) : Tree (Event Q Reply) R :=
  iter (transition step) state

def Head.render (run : S → Tree (Event Q Reply) R) :
    Head Q R S Reply → Part (Visible (Event Q Reply) R (Tree (Event Q Reply) R))
  | .stop => Part.none
  | .result value => Part.some (.ret value)
  | .request key next => Part.some (.vis (.ask key) (run ∘ next))

variable {R S T : Type u} [DecidableEq S]

/-- Follow silent successors until reaching a head or revisiting a state. -/
def headFrom (step : S → Step Q R S Reply) (remaining : Finset S) (state : S) : Head Q R S Reply :=
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

variable [DecidableEq T] [DecidableEq Q] [DecidableEq R] [∀ key, Fintype (Reply key)]

def compatible (pairs : Finset (S × T)) : Head Q R S Reply → Head Q R T Reply → Bool
  | .stop, _ => true
  | .result left, .result right => decide (left = right)
  | .request left nextL, .request right nextR =>
    if same : left = right then
      decide (∀ reply, (nextL reply, nextR (same ▸ reply)) ∈ pairs)
    else false
  | _, _ => false

/-- Compute the largest finite simulation of the normalized heads. -/
def compare (statesL : Finset S) (statesR : Finset T)
    (left : S → Step Q R S Reply) (right : T → Step Q R T Reply) (startL : S) (startR : T) : Bool :=
  decide ((startL, startR) ∈ prune
    (fun pairs (l, r) => compatible pairs (headFrom left statesL l) (headFrom right statesR r))
    (statesL ×ˢ statesR))

end Silmaril.Elgot.ITree.Finite
