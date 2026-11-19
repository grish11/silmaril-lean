module

public import Silmaril.Wasm.Region.ByteMap.Thms
public import Silmaril.Wasm.Cfg.Machine.Defs

/-! # Anchored nested Wasm byte-map candidates

Sequence paths use the existing CFG convention: segment index and arm, not the
opening instruction index. Spines explicitly relate those indices. Every child
slice is anchored by an exact decomposition of its parent's source bytes; no
re-encoding or opcode search chooses offsets. Missing/invalid paths fail closed.
-/

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.Nested
open Silmaril.Machine.Region (Range)
open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

structure Sequence where
  path : List Cfg.SeqStep
  span : Range
  body : Silmaril.Wasm.Expr

/-- Bytes after the opcode through the block type (and catches for try_table),
and raw arm bytes excluding delimiters. `elseBytes = none` distinguishes an
if without an encoded else from an explicitly encoded empty else. -/
structure Layout where
  header : List UInt8
  first : List UInt8
  elseBytes : Option (List UInt8)

structure Frame where
  segmentIndex : Nat
  instructionIndex : Nat
  instructionSpan : Range
  arm : Nat
  layout : Layout

def Sequence.PrefixChecks (input : Input) (seq : Sequence) (index : Nat) (r : Range) : Prop :=
  seq.span.start ≤ r.start ∧ r.start < r.stop ∧ r.stop ≤ seq.span.stop ∧
  parseAll? Decode.readExpr
    (((input.bytes.drop seq.span.start).take (r.start - seq.span.start)) ++ [0x0B]) =
      some (seq.body.take index) ∧
  (seq.body[index]?).isSome ∧
  parseAll? (readOne ((input.spanBytes r).length + 1)) (input.spanBytes r) = seq.body[index]?

instance (input : Input) (seq : Sequence) (index : Nat) (r : Range) :
    Decidable (seq.PrefixChecks input index r) := inferInstanceAs (Decidable (_ ∧ _))

/-- Prefix equality pins the segment's terminator to this occurrence, even
when several structured instructions are syntactically identical. -/
def Frame.Opens (f : Frame) (seq : Sequence) (instr : Silmaril.Wasm.Instr) : Prop :=
  ∃ sg ∈ (Cfg.segment seq.body)[f.segmentIndex]?.toList,
    sg.term = some instr ∧ seq.body[f.instructionIndex]? = some instr ∧
    seq.body.take f.instructionIndex =
      ((Cfg.segment seq.body).take f.segmentIndex).flatMap Cfg.Segment.instrs ++ sg.body

instance (f : Frame) (seq : Sequence) (instr : Silmaril.Wasm.Instr) :
    Decidable (f.Opens seq instr) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Exact source-byte decomposition for the four structured instruction forms.
Header parsing validates source LEBs instead of assuming their encoded length. -/
def Layout.Checks (input : Input) (r : Range) (l : Layout) : Silmaril.Wasm.Instr → Prop
  | .block bt body => l.elseBytes = none ∧
      parseAll? Decode.readBlockType l.header = some bt ∧
      parseAll? Decode.readExpr (l.first ++ [0x0B]) = some body ∧
      input.spanBytes r = [0x02] ++ l.header ++ l.first ++ [0x0B]
  | .loop bt body => l.elseBytes = none ∧
      parseAll? Decode.readBlockType l.header = some bt ∧
      parseAll? Decode.readExpr (l.first ++ [0x0B]) = some body ∧
      input.spanBytes r = [0x03] ++ l.header ++ l.first ++ [0x0B]
  | .if_ bt left right =>
      parseAll? Decode.readBlockType l.header = some bt ∧
      parseAll? Decode.readExpr (l.first ++ [0x0B]) = some left ∧
      match l.elseBytes with
      | none => right = [] ∧ input.spanBytes r = [0x04] ++ l.header ++ l.first ++ [0x0B]
      | some es => parseAll? Decode.readExpr (es ++ [0x0B]) = some right ∧
          input.spanBytes r = [0x04] ++ l.header ++ l.first ++ [0x05] ++ es ++ [0x0B]
  | .tryTable bt catches body => l.elseBytes = none ∧
      parseAll? (do let t ← Decode.readBlockType; let cs ← Decode.readVec Decode.readCatch; pure (t, cs))
        l.header = some (bt, catches) ∧
      parseAll? Decode.readExpr (l.first ++ [0x0B]) = some body ∧
      input.spanBytes r = [0x1F] ++ l.header ++ l.first ++ [0x0B]
  | _ => False

instance (input : Input) (r : Range) (l : Layout) (instr : Silmaril.Wasm.Instr) :
    Decidable (l.Checks input r instr) := by
  cases instr <;> dsimp only [Layout.Checks] <;> try infer_instance
  split <;> infer_instance

/-- Children begin after the validated source header; an encoded else adds its
actual preceding arm length and delimiter. An absent else has no byte interval. -/
def Frame.child? (f : Frame) (seq : Sequence) : Option Sequence := do
  let instr ← seq.body[f.instructionIndex]?
  let body ← Cfg.armOf instr f.arm
  let start := f.instructionSpan.start + 1 + f.layout.header.length
  if f.arm = 0 then
    pure ⟨seq.path ++ [(f.segmentIndex, f.arm)],
      ⟨start, start + f.layout.first.length, Nat.le_add_right _ _⟩, body⟩
  else if f.arm = 1 then do
    let es ← f.layout.elseBytes
    let start := start + f.layout.first.length + 1
    pure ⟨seq.path ++ [(f.segmentIndex, f.arm)],
      ⟨start, start + es.length, Nat.le_add_right _ _⟩, body⟩
  else none

def Frame.Checks (input : Input) (seq : Sequence) (f : Frame) : Prop :=
  seq.PrefixChecks input f.instructionIndex f.instructionSpan ∧
  ∃ instr ∈ seq.body[f.instructionIndex]?.toList,
    f.Opens seq instr ∧ f.layout.Checks input f.instructionSpan instr

instance (input : Input) (seq : Sequence) (f : Frame) : Decidable (f.Checks input seq) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Root is bounded inside the original function bytes; the final delimiter is
excluded from the sequence span and never an instruction row. -/
def root (input : Input) : Sequence :=
  ⟨[], ⟨input.codeStart, max input.codeStart (input.bytes.length - 1), Nat.le_max_left _ _⟩, input.body⟩

def Sequence.Encoded (input : Input) (seq : Sequence) : Prop :=
  input.codeStart ≤ seq.span.start ∧ seq.span.stop ≤ input.bytes.length ∧
  Cfg.Machine.seqAt input.body seq.path = some seq.body ∧
  Instrs Forms.all (input.spanBytes seq.span) seq.body

/-- Source ancestry is additional semantic evidence, not merely an isolated
slice that happens to decode to an equal instruction sequence. -/
inductive Located (input : Input) : Sequence → Prop where
  | root (body : input.BodyChecks) : Located input (root input)
  | child {parent child : Sequence} (ancestry : Located input parent)
      (encoded : child.Encoded input) (f : Frame) (checks : f.Checks input parent)
      (selected : f.child? parent = some child) : Located input child

/-- Candidate spine resolution checks every parent and selected child's source
encoding, bounds and existing CFG lookup. It rejects unknown children. -/
def follow? (input : Input) : Sequence → List Frame → Option Sequence
  | seq, [] => some seq
  | seq, f :: rest =>
    if f.Checks input seq then do
      let child ← f.child? seq
      if input.codeStart ≤ child.span.start ∧ child.span.stop ≤ input.bytes.length ∧
          Cfg.Machine.seqAt input.body child.path = some child.body ∧
          parseAll? Decode.readExpr (input.spanBytes child.span ++ [0x0B]) = some child.body then
        follow? input child rest
      else none
    else none

structure Candidate where
  entry : ByteMapEntry
  spine : List Frame

def Candidate.Checks (input : Input) (candidate : Candidate) : Prop :=
  ∃ seq ∈ (follow? input (root input) candidate.spine).toList,
    candidate.entry.decoded.functionIndex = input.functionIndex ∧
    candidate.entry.decoded.sequencePath = seq.path ∧
    seq.PrefixChecks input candidate.entry.decoded.instructionOffset candidate.entry.bytes

instance (input : Input) (candidate : Candidate) : Decidable (candidate.Checks input) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Nested instruction meaning includes actual source ancestry and the
existing CFG path lookup, plus encoded prefix and instruction occurrence. -/
def DecodesAt (input : Input) (label : DecodedLabel) (r : Range) : Prop :=
  ∃ seq, Located input seq ∧ label.functionIndex = input.functionIndex ∧
    label.sequencePath = seq.path ∧
    input.codeStart ≤ r.start ∧ r.start < r.stop ∧ r.stop ≤ input.bytes.length ∧
    Instrs Forms.all ((input.bytes.drop seq.span.start).take (r.start - seq.span.start))
      (seq.body.take label.instructionOffset) ∧
    ∃ instr, seq.body[label.instructionOffset]? = some instr ∧
      Binary.Core.Instr Forms.all (input.spanBytes r) instr

/-- All instruction positions in every sequence represented by the existing
CFG block inventory. Duplicate sequence paths do not change coverage. Empty
sequences contribute no instruction positions or synthetic delimiter labels. -/
def inventory (input : Input) : List DecodedLabel :=
  (Cfg.blocks input.body).flatMap fun (block, _) =>
    match Cfg.Machine.seqAt input.body block.seq with
    | none => []
    | some body => (List.range body.length).map fun k => ⟨input.functionIndex, block.seq, k⟩

def TableChecks (input : Input) (candidates : List Candidate) : Prop :=
  (∀ c ∈ candidates, c.Checks input) ∧
  (∀ c ∈ candidates, ∀ d ∈ candidates,
    c.entry.decoded = d.entry.decoded → c.entry.bytes = d.entry.bytes) ∧
  (∀ c ∈ candidates, ∀ d ∈ candidates,
    c.entry.decoded.functionIndex = d.entry.decoded.functionIndex →
    c.entry.bytes.start = d.entry.bytes.start → c.entry.decoded = d.entry.decoded)

instance (input : Input) (candidates : List Candidate) : Decidable (TableChecks input candidates) :=
  inferInstanceAs (Decidable (_ ∧ _))

structure Certified (input : Input) where
  bodyEncoding : Binary.Core.Func Forms.all input.bytes (input.localGroups.flatMap expandLocal, input.body)
  map : ValidatedByteMap (fun _ => input.bytes.length) (DecodesAt input)

end Silmaril.Wasm.Region.ByteMap.Nested
