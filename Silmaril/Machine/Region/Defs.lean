module

public import Silmaril.Semantics.Region.Semantic.Defs
public import Silmaril.Prelude.Bytes.Defs

/-! # Typed binary-region coordinates

These are layout adapters, not an ELF encoding and not an instruction semantics.
Addresses, file offsets and section-relative coordinates are deliberately distinct.
Ambiguous translations fail. Missing data denotes unknown bytes, never zeroes.
-/

@[expose] public section
namespace Silmaril.Machine.Region

/-- A non-wrapping, half-open byte/instruction range. Empty ranges are allowed
as data; semantic region validity separately requires an admitted entry. -/
structure Range where
  start : Nat
  stop : Nat
  ordered : start ≤ stop
  deriving DecidableEq

def Range.Contains (r : Range) (n : Nat) : Prop := r.start ≤ n ∧ n < r.stop
instance (r : Range) (n : Nat) : Decidable (r.Contains n) := inferInstanceAs (Decidable (_ ∧ _))

inductive CodeSpace where
  | virtual
  | section (index : Nat)
  deriving DecidableEq, Repr

structure Label where
  space : CodeSpace
  offset : Nat
  deriving DecidableEq, Repr

structure Segment where
  space : CodeSpace
  range : Range
  deriving DecidableEq

def Segment.Contains (s : Segment) (l : Label) : Prop :=
  s.space = l.space ∧ s.range.Contains l.offset
instance (s : Segment) (l : Label) : Decidable (s.Contains l) := inferInstanceAs (Decidable (_ ∧ _))

/-- Mapping code coordinates to backing-object offsets. It does not assert
that these bytes are executable instructions. -/
structure Mapping where
  code : Segment
  fileOffset : Nat

/-- Readable objects can be backed by bytes, kernel bytes, or sparse memory. -/
structure ByteSource where
  read : Nat → Option UInt8

def ByteSource.ofByteArray (b : ByteArray) : ByteSource := ⟨fun n => b[n]?⟩
def ByteSource.ofKBytes (b : Silmaril.KBytes) : ByteSource := ⟨b.get?⟩

structure BinaryObject where
  bytes : ByteSource
  layout : List Mapping

/-- All mappings owning this coordinate. -/
def owners (layout : List Mapping) (l : Label) : List Mapping :=
  layout.filter fun m => decide (m.code.Contains l)

/-- Overlapping owners are unresolved, even if they happen to map to equal bytes. -/
def translate (layout : List Mapping) (l : Label) : Option Nat :=
  match owners layout l with
  | [m] => some (m.fileOffset + (l.offset - m.code.range.start))
  | _ => none

def BinaryObject.codeByte (b : BinaryObject) (l : Label) : Option UInt8 := do
  let offset ← translate b.layout l
  b.bytes.read offset

/-- Optional data is an observation of memory, not a fabricated completion.
Semantics must quantify over all compatible concrete completions. -/
structure LoadedImage where
  code : BinaryObject
  data : Option ByteSource

/-- Every supplied data byte agrees; omitted data imposes no restrictions.
Code/execution permissions must be related separately by the ISA adapter. -/
def LoadedImage.DataCompatible (image : LoadedImage) (memory : Nat → UInt8) : Prop :=
  ∀ source, image.data = some source → ∀ n byte, source.read n = some byte → memory n = byte

/-- Expose support labels without confusing support with ordered ranges. -/
def supportLabels (ss : Finset Segment) (l : Label) : Prop := ∃ s ∈ ss, s.Contains l

end Silmaril.Machine.Region
