module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Thms
import Mathlib.Data.Finset.Card

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields

open Comparison

variable {V K F α : Type} {n a b locals : Nat}

/-- For each output slot, identify its source slot in the input packet. -/
abbrev FieldMap (width : Nat) := Fin width → Fin width

/-- The named CFG packet convention uses right-nested pairs ending in unit. -/
def packed {R : Type} : {width : Nat} → (Fin width → Val R) → Val R
  | 0, _ => .unit
  | width + 1, fields => .pair (fields 0) (packed fun i : Fin width => fields i.succ)

def encode {M : Type → Type} (model : Model F M α) : {width : Nat} → (Fin width → α) → α
  | 0, _ => model.unit
  | width + 1, fields => model.pair (fields 0) (encode model fun i : Fin width => fields i.succ)

def read? (env : V → Option (Val (Fin n))) : Val V → Option (Val (Fin n))
  | .var reg => env reg
  | .unit => some .unit
  | .pair left right => do
    let left ← read? env left
    let right ← read? env right
    return .pair left right

/-- Read a fixed-width packet of symbolic input fields. A field is opaque,
even if its runtime value happens to be a pair. -/
def fieldMap? : (width : Nat) → Val (Fin n) → Option (Fin width → Fin n)
  | 0, .unit => some Fin.elim0
  | width + 1, .pair (.var i) tail => (fieldMap? width tail).map (Fin.cons i)
  | _, _ => none

variable [DecidableEq V]

/-- Recognize value copies, pair construction and known-pair destructuring.
The symbolic updates follow the actual order, including aliased destinations. -/
def body? (env : V → Option (Val (Fin n))) : Body V K F → Option (K × FieldMap n)
  | .let1 dst (.val value) tail => do
    let shape ← read? env value
    body? (upd env dst (some shape)) tail
  | .let2 left right (.val value) tail =>
    match read? env value with
    | some (.pair fst snd) => body? (upd (upd env left (some fst)) right (some snd)) tail
    | _ => none
  | .term (.br target value) => do
    let shape ← read? env value
    let fields ← fieldMap? n shape
    return (target, fields)
  | _ => none

def block? (width : Nat) (block : Block V K F) : Option (K × FieldMap width) :=
  body? (upd (fun _ => none) block.param (some (packed fun i : Fin width => .var i))) block.body

def next? (width : Nat) (graph : Graph V F a b) (index : Fin graph.locals) :
    Option (Label graph.locals b × FieldMap width) :=
  block? width (graph.block index)

inductive Outcome (width locals outputs : Nat) where
  | returns (port : Fin outputs) (fields : FieldMap width)
  | cycle (repeated : Fin locals)
  | unsupported (index : Fin locals)

def Outcome.precompose (first : FieldMap n) : Outcome n locals b → Outcome n locals b
  | .returns port fields => .returns port (first ∘ fields)
  | .cycle i => .cycle i
  | .unsupported i => .unsupported i

/-- A label is removed only after its typed edge is checked. A repeat has
no opportunity to branch on a packet, even if the field map changes. -/
def inspect (width : Nat) (graph : Graph V F a b) (remaining : Finset (Fin graph.locals))
    (start : Label graph.locals b) : Outcome width graph.locals b :=
  match start with
  | .inr port => .returns port id
  | .inl index =>
    if _fresh : index ∈ remaining then
      match next? width graph index with
      | none => .unsupported index
      | some (target, fields) => (inspect width graph (remaining.erase index) target).precompose fields
    else .cycle index
termination_by remaining.card
decreasing_by exact Finset.card_erase_lt_of_mem _fresh

def entryOutcome (width : Nat) (graph : Graph V F a b) (input : Fin a) : Outcome width graph.locals b :=
  inspect width graph Finset.univ (graph.entry input)

/-- The observation predicted on a well-formed packet. Unsupported syntax
has no prediction, distinct from a checked cycle predicting `Part.none`. -/
def Outcome.predict (model : Model F Part α) (packet : Fin n → α) :
    Outcome n locals b → Option (Part (Fin b × α))
  | .returns port fields => some (Part.some (port, encode model (packet ∘ fields)))
  | .cycle _ => some Part.none
  | .unsupported _ => none

def Outcome.supported : Outcome n locals b → Prop
  | .unsupported _ => False
  | _ => True

/-- Every entry follows accepted blocks until a public port or a repeat. -/
def EntryTyped (width : Nat) (graph : Graph V F a b) : Prop :=
  ∀ input, (entryOutcome width graph input).supported

def Outcome.refines? {m : Nat} : Outcome n locals b → Outcome n m b → Option Bool
  | .unsupported _, _ | _, .unsupported _ => none
  | .cycle _, _ => some true
  | .returns _ _, .cycle _ => some false
  | .returns port fields, .returns port' fields' => some (decide (port = port' ∧ fields = fields'))

def refinement? (width : Nat) (left right : Graph V F a b) : Option Bool :=
  let results := (List.finRange a).map fun input =>
    (entryOutcome width left input).refines? (entryOutcome width right input)
  if results.all Option.isSome then some (results.all (· == some true)) else none

/-- Refinement on the well-formed fixed-width interface of the actual CFG. -/
def Sat (width : Nat) (model : PairModel F Part α) (left right : Graph V F a b) : Prop :=
  ∀ (input : Fin a) (packet : Fin width → α),
    left.denote model.val (input, encode model.val packet) ≤
      right.denote model.val (input, encode model.val packet)

/-- Recover syntactic equality of field maps from all packed observations. -/
def Separates (width : Nat) (model : PairModel F Part α) : Prop :=
  ∀ (left right : FieldMap width),
    (∀ packet : Fin width → α, encode model.val (packet ∘ left) = encode model.val (packet ∘ right)) →
      left = right

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields
