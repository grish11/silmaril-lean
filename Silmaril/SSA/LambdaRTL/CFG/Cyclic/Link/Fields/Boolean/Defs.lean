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

/-- A certified undefined step has a known empty observation. Unsupported
syntax carries no semantic prediction. -/
inductive Step (R : Type) where
  | next (result : R)
  | undefined
  | unsupported

def Step.predict {R A : Type} (render : R → A) : Step R → Option (Part A)
  | .next result => some (Part.some (render result))
  | .undefined => some Part.none
  | .unsupported => none

abbrev Advance (profile : Profile graph inputs outputs) :=
  At profile.localWidth → Step (At profile.width)

def pureAdvance (profile : Profile graph inputs outputs) : Advance profile :=
  fun state => match next? profile state with
    | some next => .next next
    | none => .unsupported

/-- A step agrees with actual named block execution when it has a prediction. -/
def StepSound (model : BooleanModel F α) (profile : Profile graph inputs outputs) (advance : Advance profile) : Prop :=
  ∀ state result, (advance state).predict (fun next => Sum.inr (At.render model next)) = some result →
    graph.step model.pairModel.val (.inl state.1, encodePacket model state.2) = result

def privateKeys (profile : Profile graph inputs outputs) : Finset (Fin graph.locals × List Bool) :=
  ((List.finRange graph.locals).flatMap fun label =>
    (packets (profile.localWidth label)).map fun packet =>
      At.key (⟨label, packet⟩ : At profile.localWidth)).toFinset

inductive Outcome (localWidth : Fin n → Nat) (outputs : Fin b → Nat) where
  | returns (result : At outputs)
  | cycle (repeated : At localWidth)
  | undefined (atState : At localWidth)
  | unsupported (atState : At localWidth)

/-- Remove a checked private state only after finding its next state.
The remaining set contains label/packet pairs, so a changed packet at the
same label is explored as a fresh state. -/
def inspectWith (profile : Profile graph inputs outputs) (advance : Advance profile)
    (remaining : Finset (Fin graph.locals × List Bool)) :
    At profile.width → Outcome profile.localWidth outputs
  | ⟨.inr port, packet⟩ => .returns ⟨port, packet⟩
  | ⟨.inl index, packet⟩ =>
    let current : At profile.localWidth := ⟨index, packet⟩
    if _fresh : current.key ∈ remaining then
      match advance current with
      | .unsupported => .unsupported current
      | .undefined => .undefined current
      | .next next => inspectWith profile advance (remaining.erase current.key) next
    else .cycle current
termination_by remaining.card
decreasing_by exact Finset.card_erase_lt_of_mem _fresh

def inspect (profile : Profile graph inputs outputs) (remaining : Finset (Fin graph.locals × List Bool)) :
    At profile.width → Outcome profile.localWidth outputs :=
  inspectWith profile (pureAdvance profile) remaining

def entryState (profile : Profile graph inputs outputs) (input : Fin a) (packet : Packet (inputs input)) :
    At profile.width :=
  ⟨graph.entry input, packet ∘ Fin.cast (profile.entryWidth input)⟩

def entryOutcomeWith (profile : Profile graph inputs outputs) (advance : Advance profile)
    (input : Fin a) (packet : Packet (inputs input)) :
    Outcome profile.localWidth outputs :=
  inspectWith profile advance (privateKeys profile) (entryState profile input packet)

def entryOutcome (profile : Profile graph inputs outputs) (input : Fin a) (packet : Packet (inputs input)) :
    Outcome profile.localWidth outputs :=
  entryOutcomeWith profile (pureAdvance profile) input packet

def Outcome.predict {localWidth : Fin n → Nat} (model : BooleanModel F α) :
    Outcome localWidth outputs → Option (Part (Fin b × α))
  | .returns result => some (Part.some (result.render model))
  | .cycle _ | .undefined _ => some Part.none
  | .unsupported _ => none

def Outcome.supported {localWidth : Fin n → Nat} : Outcome localWidth outputs → Prop
  | .unsupported _ => False
  | _ => True

def SupportedWith (profile : Profile graph inputs outputs) (advance : Advance profile) : Prop :=
  ∀ input packet, (entryOutcomeWith profile advance input packet).supported

/-- Every Boolean input at every port must reach a return or a checked repeat. -/
def Supported (profile : Profile graph inputs outputs) : Prop :=
  SupportedWith profile (pureAdvance profile)

def Outcome.refines? {l r : Nat} {left : Fin l → Nat} {right : Fin r → Nat} :
    Outcome left outputs → Outcome right outputs → Option Bool
  | .unsupported _, _ | _, .unsupported _ => none
  | .cycle _, _ | .undefined _, _ => some true
  | .returns _, .cycle _ | .returns _, .undefined _ => some false
  | .returns source, .returns target => some (decide (source.key = target.key))

def refinementAtWith? {left right : Graph V F a b} (first : Profile left inputs outputs)
    (second : Profile right inputs outputs) (advanceL : Advance first) (advanceR : Advance second)
    (input : Fin a) (packet : Packet (inputs input)) : Option Bool :=
  (entryOutcomeWith first advanceL input packet).refines? (entryOutcomeWith second advanceR input packet)

def refinementAt? {left right : Graph V F a b} (first : Profile left inputs outputs)
    (second : Profile right inputs outputs) (input : Fin a) (packet : Packet (inputs input)) : Option Bool :=
  refinementAtWith? first second (pureAdvance first) (pureAdvance second) input packet

def refinementWith? {left right : Graph V F a b}
    (first : Profile left inputs outputs) (second : Profile right inputs outputs)
    (advanceL : Advance first) (advanceR : Advance second) : Option Bool :=
  let results := (List.finRange a).flatMap fun input =>
    (packets (inputs input)).map (refinementAtWith? first second advanceL advanceR input)
  if results.all Option.isSome then some (results.all (· == some true)) else none

def refinement? {left right : Graph V F a b}
    (first : Profile left inputs outputs) (second : Profile right inputs outputs) : Option Bool :=
  refinementWith? first second (pureAdvance first) (pureAdvance second)

def Sat (inputs : Fin a → Nat) (model : BooleanModel F α) (left right : Graph V F a b) : Prop :=
  ∀ input (packet : Packet (inputs input)),
    left.denote model.pairModel.val (input, encodePacket model packet) ≤
      right.denote model.pairModel.val (input, encodePacket model packet)

/-- The two replies of a unary Boolean primitive. A missing reply denotes
a certified empty `Part` computation for that argument. -/
structure PrimitiveRow where
  onFalse : Option Bool
  onTrue : Option Bool

def PrimitiveRow.reply (row : PrimitiveRow) (arg : Bool) : Option Bool :=
  if arg then row.onTrue else row.onFalse

/-- A finite opcode table. Lookup uses the first matching row. An absent
opcode has no certificate. -/
abbrev PrimitiveTable (F : Type) := List (F × PrimitiveRow)

section

variable [DecidableEq F]

/-- Each row that lookup can select specifies the actual primitive
computation at both Boolean arguments. -/
def PrimitiveTable.Compatible (table : PrimitiveTable F) (model : BooleanModel F α) : Prop :=
  ∀ symbol row, table.lookup symbol = some row → ∀ arg,
    model.pairModel.val.app symbol (model.bit arg) =
      match row.reply arg with
      | some reply => Part.some (model.bit reply)
      | none => Part.none

def bitSlot (flag : Bool) : Fin 2 := if flag then 1 else 0

def slotBit : Packet 2 := fun slot => slot.val == 1

/-- Symbolic leaves index the two Boolean values. Copies and destructuring
retain packet shape, and a table reply can replace a leaf with either bit. -/
def primitiveBody (table : PrimitiveTable F) (width : K → Nat)
    (env : V → Option (Val (Fin 2))) : Body V K F → Step (At width)
  | .let1 dst (.val value) tail =>
    match read? env value with
    | some shape => primitiveBody table width (upd env dst (some shape)) tail
    | none => .unsupported
  | .let1 dst (.app symbol value) tail =>
    match read? env value, table.lookup symbol with
    | some (.var slot), some row =>
      match row.reply (slotBit slot) with
      | some reply => primitiveBody table width (upd env dst (some (.var (bitSlot reply)))) tail
      | none => .undefined
    | _, _ => .unsupported
  | .let2 left right (.val value) tail =>
    match read? env value with
    | some (.pair fst snd) =>
      primitiveBody table width (upd (upd env left (some fst)) right (some snd)) tail
    | _ => .unsupported
  | .term term =>
    match select? width slotBit env term with
    | some result => .next ⟨result.1, slotBit ∘ result.2⟩
    | none => .unsupported
  | _ => .unsupported

def primitiveBlock (table : PrimitiveTable F) (width : K → Nat)
    (block : Block V K F) (packet : Packet n) : Step (At width) :=
  primitiveBody table width
    (upd (fun _ => none) block.param (some (packed fun i => .var (bitSlot (packet i))))) block.body

def primitiveAdvance (table : PrimitiveTable F) (profile : Profile graph inputs outputs) : Advance profile :=
  fun state => primitiveBlock table profile.width (graph.block state.1) state.2

def primitiveEntryOutcome (table : PrimitiveTable F) (profile : Profile graph inputs outputs)
    (input : Fin a) (packet : Packet (inputs input)) : Outcome profile.localWidth outputs :=
  entryOutcomeWith profile (primitiveAdvance table profile) input packet

/-- Every packed input reaches a return, a repeated state, or a certified undefined step. -/
def PrimitiveSupported (table : PrimitiveTable F) (profile : Profile graph inputs outputs) : Prop :=
  SupportedWith profile (primitiveAdvance table profile)

/-- Decide inclusion of terminating exit/payload observations at every Boolean input.
A reachable unsupported step on either side leaves the comparison without a verdict. -/
def primitiveRefinement? {left right : Graph V F a b} (table : PrimitiveTable F)
    (first : Profile left inputs outputs) (second : Profile right inputs outputs) : Option Bool :=
  refinementWith? first second (primitiveAdvance table first) (primitiveAdvance table second)

end

/-- Satisfaction at stores holding Boolean packets in the designated
register, using the existing named SSA classes. -/
def packedSat {K : Type} [DecidableEq K] [Inhabited V] (width : Nat) (model : BooleanModel F α)
    (lhs rhs : SSAClass V K F Part α) : Prop :=
  ∀ (packet : Packet width) (store : V → α), store default = encodePacket model packet →
    ssaClassObserve model.pairModel lhs store ≤ ssaClassObserve model.pairModel rhs store

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean
