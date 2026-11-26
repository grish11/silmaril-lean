module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width.Defs
import Mathlib.Data.Finset.Card

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean

open Comparison
open Width (Profile)

variable {V K F α : Type} {a b n : Nat}

/-- The operational carrier can be infinite. Only packets of these two
Boolean values enter the finite checker. True takes the left arm and false
takes the right arm, binding unit in either case. -/
structure BooleanModel (F α : Type) where
  pairModel : PairModel F Part α
  bit : Bool → α
  split_bit : ∀ flag, pairModel.val.split (bit flag) =
    pure (if flag then .inl pairModel.val.unit else .inr pairModel.val.unit)

abbrev Packet (width : Nat) := Fin width → Bool
abbrev At {L : Type} (width : L → Nat) := (label : L) × Packet (width label)

def encodePacket (model : BooleanModel F α) (packet : Packet n) : α :=
  encode model.pairModel.val (model.bit ∘ packet)

def At.render {L : Type} {width : L → Nat} (model : BooleanModel F α) (state : At width) : L × α :=
  (state.1, encodePacket model state.2)

/-- An executable representation of the fields in slot order. -/
def At.key {L : Type} {width : L → Nat} (state : At width) : L × List Bool :=
  (state.1, (List.finRange (width state.1)).map state.2)

/-- Enumerate every Boolean packet, including the unique empty packet. -/
def packets : (width : Nat) → List (Packet width)
  | 0 => [Fin.elim0]
  | width + 1 => (packets width).flatMap fun tail => [Fin.cons false tail, Fin.cons true tail]

variable [DecidableEq V]

/-- Admit a single case on an input field. Its selected arm must be a jump;
the unselected arm is irrelevant to this concrete Boolean input. -/
def select? (width : K → Nat) (packet : Packet n) (env : V → Option (Val (Fin n))) :
    Term V K F → Option ((target : K) × Route n (width target))
  | .case (.val value) yes yesArm no noArm =>
    match read? env value with
    | some (.var field) =>
      if packet field then termTo? width (upd env yes (some .unit)) yesArm
      else termTo? width (upd env no (some .unit)) noArm
    | _ => none
  | term => termTo? width env term

variable {graph : Graph V F a b} {inputs : Fin a → Nat} {outputs : Fin b → Nat}

def next? (profile : Profile graph inputs outputs) (state : At profile.localWidth) : Option (At profile.width) :=
  (blockWith? (profile.localWidth state.1) (select? profile.width state.2) (graph.block state.1)).map
    fun edge => ⟨edge.1, state.2 ∘ edge.2⟩

def privateKeys (profile : Profile graph inputs outputs) : Finset (Fin graph.locals × List Bool) :=
  ((List.finRange graph.locals).flatMap fun label =>
    (packets (profile.localWidth label)).map fun packet =>
      At.key (⟨label, packet⟩ : At profile.localWidth)).toFinset

inductive Outcome (localWidth : Fin n → Nat) (outputs : Fin b → Nat) where
  | returns (result : At outputs)
  | cycle (repeated : At localWidth)
  | unsupported (atState : At localWidth)

/-- Remove a checked private state only after finding its next state.
The remaining set contains label/packet pairs, so a changed packet at the
same label is explored as a fresh state. -/
def inspect (profile : Profile graph inputs outputs) (remaining : Finset (Fin graph.locals × List Bool)) :
    At profile.width → Outcome profile.localWidth outputs
  | ⟨.inr port, packet⟩ => .returns ⟨port, packet⟩
  | ⟨.inl index, packet⟩ =>
    let current : At profile.localWidth := ⟨index, packet⟩
    if _fresh : current.key ∈ remaining then
      match next? profile current with
      | none => .unsupported current
      | some next => inspect profile (remaining.erase current.key) next
    else .cycle current
termination_by remaining.card
decreasing_by exact Finset.card_erase_lt_of_mem _fresh

def entryState (profile : Profile graph inputs outputs) (input : Fin a) (packet : Packet (inputs input)) :
    At profile.width :=
  ⟨graph.entry input, packet ∘ Fin.cast (profile.entryWidth input)⟩

def entryOutcome (profile : Profile graph inputs outputs) (input : Fin a) (packet : Packet (inputs input)) :
    Outcome profile.localWidth outputs :=
  inspect profile (privateKeys profile) (entryState profile input packet)

def Outcome.predict {localWidth : Fin n → Nat} (model : BooleanModel F α) :
    Outcome localWidth outputs → Option (Part (Fin b × α))
  | .returns result => some (Part.some (result.render model))
  | .cycle _ => some Part.none
  | .unsupported _ => none

def Outcome.supported {localWidth : Fin n → Nat} : Outcome localWidth outputs → Prop
  | .unsupported _ => False
  | _ => True

/-- Every Boolean input at every port must reach a return or a checked
repeat. Unvisited blocks and unselected arms are outside the check. -/
def Supported (profile : Profile graph inputs outputs) : Prop :=
  ∀ input packet, (entryOutcome profile input packet).supported

def Outcome.refines? {l r : Nat} {left : Fin l → Nat} {right : Fin r → Nat} :
    Outcome left outputs → Outcome right outputs → Option Bool
  | .unsupported _, _ | _, .unsupported _ => none
  | .cycle _, _ => some true
  | .returns _, .cycle _ => some false
  | .returns source, .returns target => some (decide (source.key = target.key))

def refinementAt? {left right : Graph V F a b} (first : Profile left inputs outputs)
    (second : Profile right inputs outputs) (input : Fin a) (packet : Packet (inputs input)) : Option Bool :=
  (entryOutcome first input packet).refines? (entryOutcome second input packet)

def refinement? {left right : Graph V F a b}
    (first : Profile left inputs outputs) (second : Profile right inputs outputs) : Option Bool :=
  let results := (List.finRange a).flatMap fun input =>
    (packets (inputs input)).map (refinementAt? first second input)
  if results.all Option.isSome then some (results.all (· == some true)) else none

def Sat (inputs : Fin a → Nat) (model : BooleanModel F α) (left right : Graph V F a b) : Prop :=
  ∀ input (packet : Packet (inputs input)),
    left.denote model.pairModel.val (input, encodePacket model packet) ≤
      right.denote model.pairModel.val (input, encodePacket model packet)

/-- Satisfaction at stores holding Boolean packets in the designated
register, using the existing named SSA classes. -/
def packedSat {K : Type} [DecidableEq K] [Inhabited V] (width : Nat) (model : BooleanModel F α)
    (lhs rhs : SSAClass V K F Part α) : Prop :=
  ∀ (packet : Packet width) (store : V → α), store default = encodePacket model packet →
    ssaClassObserve model.pairModel lhs store ≤ ssaClassObserve model.pairModel rhs store

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean
