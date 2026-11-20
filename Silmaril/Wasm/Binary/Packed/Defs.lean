module

public import Silmaril.Prelude.Bytes.Thms
public import Silmaril.Wasm.Binary.Core.Decode

/-! A packed reader for Core headers and section envelopes. The section body is returned as a
bounded cursor, not parsed here. This is not a replacement for `Core.decode?`. -/

@[expose] public section

namespace Silmaril.Wasm.Binary.Packed

/-- Positions are relative to the current tree. In a section cursor, the tree contains exactly
that section's payload. Only the well-formedness witness, not the unpacked bytes, is stored. -/
structure Cursor where
  source : KBytes
  wf : source.wf = true
  pos : Nat := 0

abbrev Reader := StateT Cursor (Except String)

/-- Specification view, used only in the correspondence statements. -/
def Cursor.spec (cursor : Cursor) : Core.Decode.Cursor := ⟨cursor.source.toByteArray, cursor.pos⟩

def decodeError {α : Type} (msg : String) : Reader α := do
  let cursor ← get
  throw s!"decoder: {msg} (at byte {cursor.pos})"

def readByte : Reader UInt8 := do
  let cursor ← get
  match cursor.source.get? cursor.pos with
  | none => throw s!"decoder: unexpected end of input at {cursor.pos}"
  | some byte =>
    set { cursor with pos := cursor.pos + 1 }
    pure byte

def remaining : Reader Nat := do
  let cursor ← get
  pure (cursor.source.len - cursor.pos)

/-- Consume a span and give it its own bound and position zero. No bytes are unpacked. -/
def readSlice (width : Nat) : Reader Cursor := do
  let cursor ← get
  if bound : cursor.pos + width ≤ cursor.source.len then
    set { cursor with pos := cursor.pos + width }
    pure ⟨cursor.source.slice cursor.pos width, cursor.source.wf_slice _ _ cursor.wf bound, 0⟩
  else decodeError s!"{width} bytes requested past the end"

def readU (bits : Nat) : Reader Nat := do
  let rec go (shift fuel : Nat) : Reader Nat := do
    match fuel with
    | 0 => throw "decoder: LEB128 too long"
    | fuel + 1 =>
      let byte ← readByte
      let value := (byte.toNat % 0x80) * 2 ^ shift
      if byte.toNat < 0x80 then pure value else pure (value + (← go (shift + 7) fuel))
  let value ← go 0 ((bits + 6) / 7)
  if value < 2 ^ bits then pure value else throw "decoder: LEB128 out of range"

def readS (bits : Nat) : Reader Int := do
  let rec go (shift fuel : Nat) (acc : Int) : Reader Int := do
    match fuel with
    | 0 => throw "decoder: LEB128 too long"
    | fuel + 1 =>
      let byte ← readByte
      let acc := acc + ((byte.toNat % 0x80 : Nat) : Int) * 2 ^ shift
      if byte.toNat < 0x80 then
        if byte.toNat ≥ 0x40 then pure (acc - 2 ^ (shift + 7)) else pure acc
      else go (shift + 7) fuel acc
  let value ← go 0 ((bits + 6) / 7) 0
  if -(2 ^ (bits - 1) : Int) ≤ value ∧ value < 2 ^ (bits - 1) then pure value
  else throw "decoder: signed LEB128 out of range"

/-- The only materialized bytes in header parsing are the eight-byte header itself. -/
def readHeader : Reader Unit := do
  let header ← readSlice 8
  unless header.source.toList == magic ++ version do decodeError "bad magic or version"

/-- Common section prefix: read the id and `u32` wire size, then check the enclosing bound.
This does not check section order, section ids, or section-specific content. -/
@[inline] def sectionPrefix {m : Type → Type} [Monad m] (byte : m UInt8)
    (u32 remaining : m Nat) (error : String → m Unit) : m (Nat × Nat) := do
  let id := (← byte).toNat
  let size ← u32
  unless size ≤ (← remaining) do error s!"section {id} past the end"
  pure (id, size)

/-- Read a section envelope and consume its payload without reading a byte past its end. -/
def readSection : Reader (Nat × Cursor) := do
  let (id, size) ← sectionPrefix readByte (readU 32) remaining decodeError
  pure (id, ← readSlice size)

/-- Reference envelope action using the exact prefix actions of `Core.Decode.readModule.go`,
then consuming the declared payload as raw bytes. It does not run the section-body reader. -/
def readSectionSpec : Core.Decode.DecodeM (Nat × ByteArray) := do
  let (id, size) ← sectionPrefix Core.Decode.readByte (Core.Decode.readU 32)
    Core.Decode.remaining Core.Decode.decodeError
  pure (id, ← Core.Decode.readBytes size)

/-- Header plus ordered envelopes to the end of the input. The result records `(id, size)`;
payload content, including the name in a custom section, is not validated. -/
@[inline] def scan {m : Type → Type} [Monad m] (header : m Unit) (remaining : m Nat)
    (envelope : m (Nat × Nat)) (error : {α : Type} → String → m α) : m (List (Nat × Nat)) := do
  header
  go envelope remaining error (← remaining) 0
where
  go {m : Type → Type} [Monad m] (envelope : m (Nat × Nat)) (remaining : m Nat)
      (error : {α : Type} → String → m α) (fuel last : Nat) : m (List (Nat × Nat)) := do
    if (← remaining) == 0 then return []
    match fuel with
    | 0 => error "trailing bytes"
    | fuel + 1 =>
      let frame ← envelope
      let rank := Core.Decode.sectionRank frame.1
      if frame.1 == 0 then
        pure (frame :: (← go envelope remaining error fuel last))
      else if last < rank then
        pure (frame :: (← go envelope remaining error fuel rank))
      else error s!"section {frame.1} out of order or repeated"

def readExtent : Reader (Nat × Nat) := do
  let (id, payload) ← readSection
  pure (id, payload.source.len)

def readExtentSpec : Core.Decode.DecodeM (Nat × Nat) := do
  let (id, payload) ← readSectionSpec
  pure (id, payload.size)

def scanFrames : Reader (List (Nat × Nat)) := scan readHeader remaining readExtent decodeError

def scanFramesSpec : Core.Decode.DecodeM (List (Nat × Nat)) :=
  scan Core.Decode.readHeader Core.Decode.remaining readExtentSpec Core.Decode.decodeError

/-- Both branches and the returned position are compared, including decoder error messages. -/
def Agrees {α β : Type} (project : α → β) (packed : Reader α)
    (reference : Core.Decode.DecodeM β) : Prop :=
  ∀ cursor, (packed.run cursor).map (fun (value, next) => (project value, next.spec)) =
    reference.run cursor.spec

end Silmaril.Wasm.Binary.Packed
