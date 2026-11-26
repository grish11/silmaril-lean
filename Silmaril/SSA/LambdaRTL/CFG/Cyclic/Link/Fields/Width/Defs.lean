module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.Defs
import Mathlib.Data.Finset.Card

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width

open Comparison

variable {V F α : Type} [DecidableEq V] {a b c locals source middle : Nat}

/-- A width for every label, with a certificate that each public input has
the width required by its entry address. The checker validates block jumps
against their target widths as it visits them. -/
structure Profile (graph : Graph V F a b) (inputs : Fin a → Nat) (outputs : Fin b → Nat) where
  localWidth : Fin graph.locals → Nat
  entryWidth : ∀ i, Sum.elim localWidth outputs (graph.entry i) = inputs i

abbrev Profile.width {graph : Graph V F a b} {inputs : Fin a → Nat} {outputs : Fin b → Nat}
    (profile : Profile graph inputs outputs) : Label graph.locals b → Nat :=
  Sum.elim profile.localWidth outputs

/-- Check the entry-width certificate for a proposed profile. -/
def Profile.certify (graph : Graph V F a b) (inputs : Fin a → Nat) (outputs : Fin b → Nat)
    (localWidth : Fin graph.locals → Nat) : Option (Profile graph inputs outputs) :=
  if valid : ∀ i, Sum.elim localWidth outputs (graph.entry i) = inputs i then
    some ⟨localWidth, valid⟩
  else none

section Link

variable [Inhabited V] {left : Graph V F a b} {right : Graph V F b c}
  {inputs : Fin a → Nat} {mids : Fin b → Nat} {outputs : Fin c → Nat}

/-- A handoff keeps the width specified by the shared middle interface. -/
def Profile.link (first : Profile left inputs mids) (second : Profile right mids outputs) :
    Profile (left.link right) inputs outputs where
  localWidth := Fin.addCases (Fin.addCases first.localWidth mids) second.localWidth
  entryWidth input := by
    have width (label : Label left.locals b) :
        Sum.elim (Fin.addCases (Fin.addCases first.localWidth mids) second.localWidth) outputs
          (left.leftLabel right label) = first.width label := by
      cases label with
      | inl i =>
        change Fin.addCases (Fin.addCases first.localWidth mids) second.localWidth
          ((i.castAdd b).castAdd right.locals) = first.localWidth i
        simp
      | inr port =>
        change Fin.addCases (Fin.addCases first.localWidth mids) second.localWidth
          ((port.natAdd left.locals).castAdd right.locals) = mids port
        simp
    exact (width (left.entry input)).trans (first.entryWidth input)

end Link

variable {graph : Graph V F a b} {inputs : Fin a → Nat} {outputs : Fin b → Nat}

/-- Primitive relabelling leaves the layout and width certificate intact. -/
def Profile.mapOp {F' : Type} (profile : Profile graph inputs outputs) (rename : F → F') :
    Profile (graph.mapOp rename) inputs outputs :=
  ⟨profile.localWidth, profile.entryWidth⟩

def next? (profile : Profile graph inputs outputs) (index : Fin graph.locals) :
    Option ((target : Label graph.locals b) × Route (profile.localWidth index) (profile.width target)) :=
  blockTo? (profile.localWidth index) profile.width (graph.block index)

inductive Outcome (source locals : Nat) (outputs : Fin b → Nat) where
  | returns (port : Fin b) (route : Route source (outputs port))
  | cycle (repeated : Fin locals)
  | unsupported (index : Fin locals)

def Outcome.precompose (first : Route source middle) : Outcome middle locals outputs → Outcome source locals outputs
  | .returns port route => .returns port (first ∘ route)
  | .cycle i => .cycle i
  | .unsupported i => .unsupported i

/-- Each successful jump selects fields at its actual target width.
Repeated labels are checked before they leave the remaining set. -/
def inspect (profile : Profile graph inputs outputs) (remaining : Finset (Fin graph.locals))
    (start : Label graph.locals b) : Outcome (profile.width start) graph.locals outputs :=
  match start with
  | .inr port => .returns port id
  | .inl index =>
    if _fresh : index ∈ remaining then
      match next? profile index with
      | none => .unsupported index
      | some ⟨target, route⟩ => (inspect profile (remaining.erase index) target).precompose route
    else .cycle index
termination_by remaining.card
decreasing_by exact Finset.card_erase_lt_of_mem _fresh

def entryOutcome (profile : Profile graph inputs outputs) (input : Fin a) :
    Outcome (inputs input) graph.locals outputs :=
  (inspect profile Finset.univ (graph.entry input)).precompose (Fin.cast (profile.entryWidth input))

/-- Unsupported syntax has no prediction. A checked cycle predicts an
undefined `Part` result on packed input. -/
def Outcome.predict (model : Model F Part α) (packet : Fin source → α) :
    Outcome source locals outputs → Option (Part (Fin b × α))
  | .returns port route => some (Part.some (port, encode model (packet ∘ route)))
  | .cycle _ => some Part.none
  | .unsupported _ => none

def Outcome.supported : Outcome source locals outputs → Prop
  | .unsupported _ => False
  | _ => True

def EntryTyped (profile : Profile graph inputs outputs) : Prop :=
  ∀ input, (entryOutcome profile input).supported

def Outcome.refines? {r : Nat} : Outcome source locals outputs → Outcome source r outputs → Option Bool
  | .unsupported _, _ | _, .unsupported _ => none
  | .cycle _, _ => some true
  | .returns _ _, .cycle _ => some false
  | .returns port route, .returns port' route' =>
    some (if same : port = port' then decide (route = (same.symm ▸ route' : Route source (outputs port))) else false)

def refinement? {left right : Graph V F a b}
    (first : Profile left inputs outputs) (second : Profile right inputs outputs) : Option Bool :=
  let results := (List.finRange a).map fun input =>
    (entryOutcome first input).refines? (entryOutcome second input)
  if results.all Option.isSome then some (results.all (· == some true)) else none

/-- Actual exit/payload inclusion on the packed input interface. -/
def Sat (inputs : Fin a → Nat) (model : PairModel F Part α) (left right : Graph V F a b) : Prop :=
  ∀ (input : Fin a) (packet : Fin (inputs input) → α),
    left.denote model.val (input, encode model.val packet) ≤
      right.denote model.val (input, encode model.val packet)

def Separates (inputs : Fin a → Nat) (outputs : Fin b → Nat) (model : PairModel F Part α) : Prop :=
  ∀ i j, SeparatesWidths (inputs i) (outputs j) model

/-- The usual named SSA comparison, restricted to stores with a packet of
the given width in the designated register. It uses the existing sentence
sides and pair-lawful `Part` model. -/
def packedSat {K : Type} [DecidableEq K] [Inhabited V] (width : Nat) (model : PairModel F Part α)
    (lhs rhs : SSAClass V K F Part α) : Prop :=
  ∀ (packet : Fin width → α) (store : V → α), store default = encode model.val packet →
    ssaClassObserve model lhs store ≤ ssaClassObserve model rhs store

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width
