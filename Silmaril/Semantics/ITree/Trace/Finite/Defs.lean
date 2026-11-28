module

public import Silmaril.Semantics.ITree.Reindex.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Pi

/-! Finite-state weak trace comparison with finite request-indexed replies. -/

@[expose] public section

namespace Silmaril.Elgot.ITree.Finite

universe u v

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

/-- A stateless handler admits a completed exchange according to its
request key and the actual typed reply. -/
def replyHandler (admits : ∀ key, Reply key → Bool) : Handler Unit (Event Q Reply)
  | ⟨_, .ask key⟩, _, reply, _ => admits key reply = true

variable {H : Type v}

/-- A completed exchange either has one next handler state or is denied.
The event key and reply retain their original types. -/
def statefulReplyHandler (advance : H → ∀ key, Reply key → Option H) : Handler H (Event Q Reply)
  | ⟨_, .ask key⟩, h, reply, h' => advance h key reply = some h'

variable [DecidableEq T] [DecidableEq Q] [DecidableEq R] [∀ key, Fintype (Reply key)]

def compatibleUsing (follow : ∀ key, Reply key → S → T → Prop)
    [∀ key reply s t, Decidable (follow key reply s t)] :
    Head Q R S Reply → Head Q R T Reply → Bool
  | .stop, _ => true
  | .result left, .result right => decide (left = right)
  | .request left nextL, .request right nextR =>
    if same : left = right then
      decide (∀ reply, follow left reply (nextL reply) (nextR (same ▸ reply)))
    else false
  | _, _ => false

def compatibleUnder (admits : ∀ key, Reply key → Bool) (pairs : Finset (S × T)) :
    Head Q R S Reply → Head Q R T Reply → Bool :=
  compatibleUsing (fun key reply s t => admits key reply = true → (s, t) ∈ pairs)

abbrev compatible (pairs : Finset (S × T)) : Head Q R S Reply → Head Q R T Reply → Bool :=
  compatibleUnder (fun _ _ => true) pairs

/-- Prune successor obligations for denied replies. Request keys are still
compared even when the handler admits no reply to a request. -/
def compareUnder (admits : ∀ key, Reply key → Bool) (statesL : Finset S) (statesR : Finset T)
    (left : S → Step Q R S Reply) (right : T → Step Q R T Reply) (startL : S) (startR : T) : Bool :=
  decide ((startL, startR) ∈ prune
    (fun pairs (l, r) => compatibleUnder admits pairs (headFrom left statesL l) (headFrom right statesR r))
    (statesL ×ˢ statesR))

/-- Compute the largest finite simulation of the normalized heads. -/
def compare (statesL : Finset S) (statesR : Finset T)
    (left : S → Step Q R S Reply) (right : T → Step Q R T Reply) (startL : S) (startR : T) : Bool :=
  compareUnder (fun _ _ => true) statesL statesR left right startL startR

/-- Check the single successor of an admitted exchange. -/
def handlerSuccessor [DecidableEq H] (pairs : Finset ((S × T) × H)) (s : S) (t : T) :
    Option H → Prop
  | none => True
  | some h => ((s, t), h) ∈ pairs

instance [DecidableEq H] (pairs : Finset ((S × T) × H)) (s : S) (t : T) (next : Option H) :
    Decidable (handlerSuccessor pairs s t next) :=
  match next with
  | none => isTrue trivial
  | some h => inferInstanceAs (Decidable (((s, t), h) ∈ pairs))

/-- Prune the product of two graph states and one shared handler state.
Silent normalization is independent of the handler. Pending requests
still compare their keys even when every reply is denied. -/
def compareWithHandler [DecidableEq H] (advance : H → ∀ key, Reply key → Option H)
    (statesL : Finset S) (statesR : Finset T) (statesH : Finset H)
    (left : S → Step Q R S Reply) (right : T → Step Q R T Reply)
    (startL : S) (startR : T) (startH : H) : Bool :=
  decide (((startL, startR), startH) ∈ prune (fun pairs ((s, t), h) =>
    compatibleUsing (fun key reply nextL nextR => handlerSuccessor pairs nextL nextR (advance h key reply))
      (headFrom left statesL s) (headFrom right statesR t))
    ((statesL ×ˢ statesR) ×ˢ statesH))

end Silmaril.Elgot.ITree.Finite
