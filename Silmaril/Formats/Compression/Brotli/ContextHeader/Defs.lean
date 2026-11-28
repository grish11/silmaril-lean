module

public import Silmaril.Formats.Compression.Brotli.BlockTypes.Defs

/-! The RFC 7932 §9.2 prefix following the block controls. Read
NPOSTFIX, the four-bit NDIRECT field and one context mode per literal
block type. Stop before the literal context map. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.ContextHeader

inductive Mode where
  | lsb6 | msb6 | utf8 | signed
  deriving DecidableEq, Repr

def Mode.code : Mode → Nat
  | .lsb6 => 0
  | .msb6 => 1
  | .utf8 => 2
  | .signed => 3

structure Fields where
  postfixBits : Fin 4
  directField : Fin 16
  modes : List Mode
  deriving DecidableEq, Repr

def Fields.direct (fields : Fields) : Nat :=
  fields.directField.val * 2 ^ fields.postfixBits.val

/-- RFC 7932 §3.3's standard distance-code alphabet size. -/
def Fields.distanceAlphabet (fields : Fields) : Nat :=
  16 + fields.direct + 48 * 2 ^ fields.postfixBits.val

def Fields.bits (fields : Fields) : List Bool :=
  natBits fields.postfixBits.val 2 ++ natBits fields.directField.val 4 ++
    fields.modes.flatMap (fun mode => natBits mode.code 2)

def Wire (literalTypes : Nat) (bits : List Bool) (fields : Fields) : Prop :=
  1 ≤ literalTypes ∧ literalTypes ≤ 256 ∧ fields.modes.length = literalTypes ∧ bits = fields.bits

structure Header where
  controls : BlockTypes.Controls
  fields : Fields

def Header.Wire (bits : List Bool) (header : Header) : Prop :=
  ∃ controls fields,
    bits = controls ++ fields ∧ BlockTypes.Wire controls header.controls ∧
      ContextHeader.Wire header.controls.literal.typeCount fields header.fields

inductive Error where
  | invalidLiteralTypes
  | bitLimit
  | truncated
  | controls (reason : BlockTypes.Error)
  deriving DecidableEq, Repr

namespace Internal

def take (reader : LSBReader) (width : Nat) : Except Error (Nat × LSBReader) :=
  match reader.readBits width with
  | none => .error .truncated
  | some pair => .ok pair

def mode (code : Nat) : Mode :=
  match code with
  | 0 => .lsb6
  | 1 => .msb6
  | 2 => .utf8
  | _ => .signed

def readModes : Nat → LSBReader → Except Error (List Mode × LSBReader)
  | 0, reader => .ok ([], reader)
  | count + 1, reader => do
    let (code, next) ← take reader 2
    let (tail, after) ← readModes count next
    pure (mode code :: tail, after)

end Internal

/-- Read the fixed-size suffix at the cursor immediately after the
    controls. Guard the full extent before reading any field. -/
def readAfter (literalTypes bitLimit : Nat) (before : LSBReader) : Except Error (Fields × LSBReader) :=
  if literalTypes = 0 ∨ 256 < literalTypes then .error .invalidLiteralTypes
  else if bitLimit < 6 + 2 * literalTypes then .error .bitLimit
  else do
    let (postfixBits, next) ← Internal.take before 2
    let (directField, next) ← Internal.take next 4
    let (modes, after) ← Internal.readModes literalTypes next
    pure (⟨Fin.ofNat 4 postfixBits, Fin.ofNat 16 directField, modes⟩, after)

/-- Read the three controls and these fields under one bit budget.
    Call at NBLTYPESL in an already identified compressed meta-block. -/
def read (bitLimit : Nat) (before : LSBReader) : Except Error (Header × LSBReader) := do
  let (controls, postControls) ← (BlockTypes.read bitLimit before).mapError Error.controls
  let remaining := bitLimit - (postControls.totalRead - before.totalRead)
  let (fields, after) ← readAfter controls.literal.typeCount remaining postControls
  pure (⟨controls, fields⟩, after)

end Silmaril.Formats.Compression.Brotli.ContextHeader
