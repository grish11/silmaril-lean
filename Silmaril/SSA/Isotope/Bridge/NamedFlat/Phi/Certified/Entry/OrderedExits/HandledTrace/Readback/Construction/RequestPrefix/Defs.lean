module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.Defs

/-! # Split a typed finite request prefix at a selected row -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix

open LambdaSSA (FiniteCFG Region Tm)
open Silmaril.SSA.LambdaRTL (Val)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
  (Branch Expr PacketType PrimitiveSignature Slot elaborateArg elaborateBranch)

variable {F : Type} {exits blocks captures count : Nat} {Γ : List PacketType}
  {sig : PrimitiveSignature F} {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}

/-- A finite tree of structural sum cases and literal, typed jumps in the
public branch grammar. The leaves target old blocks or ordered exits. -/
abbrev CaseTail (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (Γ : List PacketType) :=
  Branch (Sum.elim packets outputs) Γ

/-- Each request extends the scope with exactly its typed reply. The tail
supplies a structural packet directly or selects through a typed branch tree. -/
inductive Row (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType)
    (outputs : Fin exits → PacketType) : List PacketType → Type
  | exit {Γ : List PacketType} (port : Fin exits) (value : Expr Γ (outputs port)) : Row sig packets outputs Γ
  | jump {Γ : List PacketType} (target : Fin blocks) (value : Expr Γ (packets target)) : Row sig packets outputs Γ
  | branch {Γ : List PacketType} (tail : CaseTail packets outputs Γ) : Row sig packets outputs Γ
  | request {Γ : List PacketType} (op : F) (arg : Expr Γ (sig.argument op))
      (tail : Row sig packets outputs (sig.reply op :: Γ)) : Row sig packets outputs Γ

abbrev Positions (Γ : List PacketType) := ∀ {ty}, Slot Γ ty → Nat

def position : {Γ : List PacketType} → {ty : PacketType} → Slot Γ ty → Nat
  | _, _, .here => 0
  | _, _, .there old => position old + 1

/-- A case payload occupies slot zero and shifts every retained slot. -/
def bindPosition {ty : PacketType} (layout : Positions Γ) : Positions (ty :: Γ) :=
  fun {_} slot => match slot with
    | .here => 0
    | .there old => layout old + 1

/-- Erase a structural expression in the supplied typed slot layout. -/
def operand (atSlot : Positions Γ) : {ty : PacketType} → Expr Γ ty → Tm F
  | _, .var slot => .var (atSlot slot)
  | _, .unit => .unit
  | _, .pair x y => .pair (operand atSlot x) (operand atSlot y)

def CaseTail.erase {newBlocks : Nat} (old : Fin blocks → Fin newBlocks) :
    {Γ : List PacketType} → Positions Γ → CaseTail packets outputs Γ → Region F
  | _, layout, .jump label packet =>
    .br (Sum.elim (fun i => (old i).val) (fun port => newBlocks + port.val) label) (operand layout packet)
  | _, layout, .case test left right =>
    .case (operand layout test) (CaseTail.erase old (bindPosition layout) left)
      (CaseTail.erase old (bindPosition layout) right)

def Row.erase : {Γ : List PacketType} → Row sig packets outputs Γ → Region F
  | _, .exit i value => .br (blocks + i.val) (operand position value)
  | _, .jump i value => .br i.val (operand position value)
  | _, .branch tail => CaseTail.erase id position tail
  | _, .request op arg tail => .let₁ (.op op (operand position arg)) tail.erase

/-- Read structural operands with the existing public expression elaborator. -/
def readRow (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType) :
    (Γ : List PacketType) → Region F → Option (Row sig packets outputs Γ)
  | Γ, .br label value =>
    if h : label < blocks then do
      let target : Fin blocks := ⟨label, h⟩
      return .jump target (← elaborateArg Γ (packets target) value)
    else if h : label - blocks < exits then do
      let port : Fin exits := ⟨label - blocks, h⟩
      return .exit port (← elaborateArg Γ (outputs port) value)
    else none
  | Γ, .case test left right =>
    (elaborateBranch (Sum.elim packets outputs) Γ (.case test left right)).map Row.branch
  | Γ, .let₁ (.op op arg) tail => do
    return .request op (← elaborateArg Γ (sig.argument op) arg)
      (← readRow sig packets outputs (sig.reply op :: Γ) tail)
  | _, _ => none

/-- The live packet stores the original input, then one nested product for
each reply. A one-slot frame uses the original packet type directly. -/
inductive Frame : List PacketType → Type
  | entry (packet : PacketType) : Frame [packet]
  | push {Γ : List PacketType} (ty : PacketType) (prev : Frame Γ) : Frame (ty :: Γ)

def Frame.packet : {Γ : List PacketType} → Frame Γ → PacketType
  | _, .entry packet => packet
  | _, .push ty prev => .product prev.packet ty

/-- Number of positional slots introduced by unpacking the frame. -/
def Frame.shift : {Γ : List PacketType} → Frame Γ → Nat
  | _, .entry _ => 0
  | _, .push _ prev => prev.shift + 2

def Frame.unpack : {Γ : List PacketType} → Frame Γ → Nat → Region F → Region F
  | _, .entry _, _, body => body
  | _, .push _ prev, index, body => .let₂ (.var index) (prev.unpack 1 body)

/-- After the older products are unpacked, the newest reply has moved by
exactly the older frame's shift. Older slots recurse through its left field. -/
def Frame.position : {Γ : List PacketType} → Frame Γ → Nat → Positions Γ
  | _, .entry _, index, _, .here => index
  | _, .push _ prev, _, _, .here => prev.shift
  | _, .push _ prev, _, _, .there slot => prev.position 1 slot

def Row.requests : {Γ : List PacketType} → Row sig packets outputs Γ → Nat
  | _, .exit .. | _, .jump .. | _, .branch .. => 0
  | _, .request _ _ tail => tail.requests + 1

/-- Old labels stay at their indices. Fresh continuation labels occupy the
appended suffix, and absolute outward labels move past that suffix. -/
def oldLabel (count : Nat) (i : Fin blocks) : Fin (blocks + count) := i.castAdd count

def freshLabel (blocks : Nat) (i : Fin count) : Fin (blocks + count) := i.natAdd blocks

def chainLabel (start : Fin blocks) (count : Nat) : Fin (count + 1) → Fin (blocks + count) :=
  Fin.cases (oldLabel count start) (freshLabel blocks)

def moveExit (blocks count label : Nat) : Nat :=
  if label < blocks then label else blocks + count + (label - blocks)

/-- The public request forwards the unmodified frame and the new reply
to the supplied continuation label. -/
def Frame.requestCell {newBlocks : Nat} (frame : Frame Γ) (op : F) (arg : Expr Γ (sig.argument op))
    (next : Fin newBlocks) : Region F :=
  frame.unpack 0 (.let₁ (.op op (operand (frame.position 0) arg))
    (.br next.val (.pair (.var (frame.shift + 1)) (.var 0))))

/-- Emit one public row per request followed by the pure tail. A request
forwards the entire frame paired with its reply to the next fresh row.
Every tail leaf uses the old label embedding or the relocated exit. -/
def Row.cells {newBlocks : Nat} (old : Fin blocks → Fin newBlocks) :
    {Γ : List PacketType} → (row : Row sig packets outputs Γ) →
    Frame Γ → (Fin (row.requests + 1) → Fin newBlocks) → Fin (row.requests + 1) → PacketType × Region F
  | _, .exit port value, frame, _, _ =>
    (frame.packet, frame.unpack 0 (.br (newBlocks + port.val) (operand (frame.position 0) value)))
  | _, .jump target value, frame, _, _ =>
    (frame.packet, frame.unpack 0 (.br (old target).val (operand (frame.position 0) value)))
  | _, .branch tail, frame, _, _ =>
    (frame.packet, frame.unpack 0 (CaseTail.erase old (frame.position 0) tail))
  | _, .request op arg tail, frame, labels, i =>
    Fin.cases
      (frame.packet, frame.requestCell op arg (labels (0 : Fin (tail.requests + 1)).succ))
      (fun k => tail.cells old (.push (sig.reply op) frame) (labels ∘ Fin.succ) k) i

/-- Exact provenance for the selected original row and the structural entry. -/
structure Shape (sig : PrimitiveSignature F) (outputs : Fin exits → PacketType)
    (packets : Fin blocks → PacketType) (source : FiniteCFG F blocks exits captures) where
  entry : Fin blocks
  selected : Fin blocks
  seed : Val (Fin captures)
  row : Row sig packets outputs [packets selected]
  entry_eq : source.entry.erase = .br entry.val (packetTerm seed)
  row_eq : (source.block selected).erase = row.erase

variable {source : FiniteCFG F blocks exits captures}

/-- Recheck exact erasure at the readback boundary. The default selects the
entry row. An explicit selection is checked independently of reachability. -/
def read [DecidableEq F] (sig : PrimitiveSignature F) (outputs : Fin exits → PacketType)
    (packets : Fin blocks → PacketType) (source : FiniteCFG F blocks exits captures)
    (selected : Option (Fin blocks) := none) : Option (Shape sig outputs packets source) := do
  let entry ← readEntry source
  let picked := selected.getD entry.val.1
  let row ← readRow sig packets outputs [packets picked] (source.block picked).erase
  let exactRow ← commonRow (blocks + exits) (source.block picked).erase (row.erase)
  return ⟨entry.val.1, picked, entry.val.2, row, entry.property,
    exactRow.property.1.trans exactRow.property.2.symm⟩

def Shape.chain (s : Shape sig outputs packets source) :
    Fin (s.row.requests + 1) → PacketType × Region F :=
  s.row.cells (oldLabel s.row.requests) (.entry (packets s.selected))
    (chainLabel s.selected s.row.requests)

/-- Preserve all old positions and their types. The selected position takes
the first row of the chain and the fresh suffix contains its continuations. -/
def Shape.table (s : Shape sig outputs packets source) :
    Fin (blocks + s.row.requests) → PacketType × Region F :=
  Fin.addCases
    (fun i => if i = s.selected then s.chain 0 else
      (packets i, (source.block i).erase.renameLabels (moveExit blocks s.row.requests)))
    (fun i => s.chain i.succ)

structure Emitted (s : Shape sig outputs packets source) where
  code : FiniteCFG F (blocks + s.row.requests) exits captures
  entry_eq : code.entry.erase = source.entry.erase
  row_eq : ∀ i, (code.block i).erase = (s.table i).2

def emit (s : Shape sig outputs packets source) : Option (Emitted s) := do
  let labels := blocks + s.row.requests + exits
  let entry ← scopedRow labels captures source.entry.erase
  let rows ← tabulateDependent (blocks + s.row.requests) fun i =>
    scopedRow labels (captures + 1) (s.table i).2
  return ⟨⟨entry.val, fun i => (rows i).val⟩, entry.property, fun i => (rows i).property⟩

structure Checked (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  shape : Shape sig outputs packets source
  emitted : Emitted shape
  sourceTyped : letI := sig.typing; source.HasType context packets outputs
  splitTyped : letI := sig.typing;
    emitted.code.HasType context (fun i => (shape.table i).1) outputs

/-- Check the original and relocated packet profiles against the actual
tables. Public construction independently checks the dispatcher grammar. -/
def check [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) (selected : Option (Fin blocks) := none) :
    Option (Checked sig context packets outputs source) :=
  letI := sig.typing;
  if old : NamedFlat.check source context packets outputs = true then do
    let shape ← read sig outputs packets source selected
    let result ← emit shape
    if new : NamedFlat.check result.code context (fun i => (shape.table i).1) outputs = true then do
      return ⟨shape, result, NamedFlat.check_sound _ _ _ _ old, NamedFlat.check_sound _ _ _ _ new⟩
    else none
  else none

section Execution

open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Primitive Transfer BlockInput)
open Silmaril.Elgot.ITree (Tree diverge)

universe u w
variable {α : Type u} {E : Type w → Type w}

/-- Raw values indexed by the logical typed slots. The split preserves the
actual tree even for a raw primitive interpretation with untyped replies. -/
abbrev Values (Γ : List PacketType) (α : Type u) := ∀ {ty}, Slot Γ ty → Value α

def bindReply {ty : PacketType} (values : Values Γ α) (value : Value α) : Values (ty :: Γ) α :=
  fun {_} slot => match slot with
    | .here => value
    | .there old => values old

def readSlots (slots : Positions Γ) (env : Env α) : Values Γ α :=
  fun {_} slot => env (slots slot)

def evalOperand (values : Values Γ α) : {ty : PacketType} → Expr Γ ty → Value α
  | _, .var slot => values slot
  | _, .unit => .unit
  | _, .pair x y => .pair (evalOperand values x) (evalOperand values y)

def Frame.pack : {Γ : List PacketType} → Frame Γ → Values Γ α → Value α
  | _, .entry _, values => values .here
  | _, .push _ prev, values => .pair (prev.pack (fun slot => values (.there slot))) (values .here)

def Frame.load : {Γ : List PacketType} → Frame Γ → Values Γ α → Env α → Env α
  | _, .entry _, _, env => env
  | _, .push _ prev, values, env =>
    let older : Values _ α := fun slot => values (.there slot)
    prev.load older (extend (extend env (prev.pack older)) (values .here))

/-- Interpret a pure tail using the payload of each selected case. The raw
evaluator diverges on an ill-shaped sum just as the flat evaluator does. -/
def CaseTail.run :
    {Γ : List PacketType} → Values Γ α → CaseTail packets outputs Γ → Tree E (Transfer α ⊕ BlockInput α blocks)
  | _, values, .jump label packet =>
    let value := evalOperand values packet
    match label with
    | .inl target => pure (.inr (target, value))
    | .inr port => pure (.inl (port.val, value))
  | _, values, .case test left right =>
    match evalOperand values test with
    | .inl payload => CaseTail.run (bindReply values payload) left
    | .inr payload => CaseTail.run (bindReply values payload) right
    | _ => diverge

/-- The finite row semantics uses the same primitive trees as the flat
evaluator. It returns either the relative ordered exit or an old block transfer. -/
def Row.run (instr : Primitive E F α) :
    {Γ : List PacketType} → Row sig packets outputs Γ → Values Γ α → Tree E (Transfer α ⊕ BlockInput α blocks)
  | _, .exit port value, values => pure (.inl (port.val, evalOperand values value))
  | _, .jump target value, values => pure (.inr (target, evalOperand values value))
  | _, .branch tail, values => CaseTail.run values tail
  | _, .request op arg tail, values =>
    instr op (evalOperand values arg) >>= fun reply => tail.run instr (bindReply values reply)

end Execution

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix
