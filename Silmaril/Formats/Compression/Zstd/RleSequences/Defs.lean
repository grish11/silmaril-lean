module

public import Silmaril.Formats.Compression.Zstd.LiteralBlock.Defs
public import Silmaril.Formats.Compression.Zstd.ReverseBits.Defs
public import Silmaril.Formats.Compression.Zstd.Sequence.Defs

/-! # Zstandard sequence sections with three RLE tables

RFC 8878 §3.1.1.3.2.1. This profile reads an exact sequence section and
produces offset values before repeat resolution.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.RleSequences

structure Limits where
  input : Nat
  commands : Nat
  deriving DecidableEq, Repr

def Limits.inputCapacity (limits : Limits) : Nat := min limits.input 131072

inductive Error where
  | inputLimit
  | commandLimit
  | truncated
  | trailingInput
  | reservedModeBits
  | unsupportedModes (byte : UInt8)
  | invalidLiteralCode
  | invalidOffsetCode
  | invalidMatchCode
  | badEndMarker
  | bitUnderflow
  | trailingBits
  deriving DecidableEq, Repr

structure Code where
  base : Nat
  width : Nat
  deriving DecidableEq, Repr

structure Codes where
  literals : Code
  offset : Code
  matched : Code
  deriving DecidableEq, Repr

/-- Table 16, codes 16 to 35. -/
def literalExtended : List Code :=
  [⟨16, 1⟩, ⟨18, 1⟩, ⟨20, 1⟩, ⟨22, 1⟩, ⟨24, 2⟩, ⟨28, 2⟩,
   ⟨32, 3⟩, ⟨40, 3⟩, ⟨48, 4⟩, ⟨64, 6⟩, ⟨128, 7⟩, ⟨256, 8⟩,
   ⟨512, 9⟩, ⟨1024, 10⟩, ⟨2048, 11⟩, ⟨4096, 12⟩, ⟨8192, 13⟩,
   ⟨16384, 14⟩, ⟨32768, 15⟩, ⟨65536, 16⟩]

/-- Table 17, codes 32 to 52. -/
def matchExtended : List Code :=
  [⟨35, 1⟩, ⟨37, 1⟩, ⟨39, 1⟩, ⟨41, 1⟩, ⟨43, 2⟩, ⟨47, 2⟩,
   ⟨51, 3⟩, ⟨59, 3⟩, ⟨67, 4⟩, ⟨83, 4⟩, ⟨99, 5⟩, ⟨131, 7⟩,
   ⟨259, 8⟩, ⟨515, 9⟩, ⟨1027, 10⟩, ⟨2051, 11⟩, ⟨4099, 12⟩,
   ⟨8195, 13⟩, ⟨16387, 14⟩, ⟨32771, 15⟩, ⟨65539, 16⟩]

def literalCode (n : Nat) : Option Code :=
  if n < 16 then some ⟨n, 0⟩ else literalExtended[n - 16]?

def matchCode (n : Nat) : Option Code :=
  if n < 32 then some ⟨n + 3, 0⟩ else matchExtended[n - 32]?

/-- Resolve all three RLE symbols. The largest supported offset symbol is 31. -/
def tables (literal offset matched : UInt8) : Except Error Codes := do
  let some ll := literalCode literal.toNat | throw .invalidLiteralCode
  if 31 < offset.toNat then throw .invalidOffsetCode
  let some ml := matchCode matched.toNat | throw .invalidMatchCode
  return ⟨ll, ⟨2 ^ offset.toNat, offset.toNat⟩, ml⟩

/-- Fields appear in decoder order: offset, match length, literal length. -/
inductive CommandWire (codes : Codes) : List Bit → Sequence.Command → Prop where
  | fields (offset matched literals : List Bit) :
      offset.length = codes.offset.width → matched.length = codes.matched.width →
      literals.length = codes.literals.width →
      CommandWire codes (offset ++ matched ++ literals)
        ⟨codes.literals.base + Bit.bitsToNatMSB literals,
          codes.offset.base + Bit.bitsToNatMSB offset, codes.matched.base + Bit.bitsToNatMSB matched⟩

inductive CommandsWire (codes : Codes) : List Bit → List Sequence.Command → Prop where
  | nil : CommandsWire codes [] []
  | cons {field tail : List Bit} {command : Sequence.Command} {commands : List Sequence.Command} :
      CommandWire codes field command → CommandsWire codes tail commands →
      CommandsWire codes (field ++ tail) (command :: commands)

/-- Exact wire relation, including a count-only zero section and the fixed
    RLE mode byte, three symbols, end marker and entire payload otherwise. -/
inductive SectionWire : List UInt8 → List Sequence.Command → Prop where
  | zero {encoded : List UInt8} : LiteralBlock.SequenceCountWire encoded 0 → SectionWire encoded []
  | rle {encoded stream : List UInt8} {literal offset matched : UInt8}
      {cursor : ReverseBits.Cursor} {codes : Codes} {commands : List Sequence.Command} :
      LiteralBlock.SequenceCountWire encoded commands.length → 0 < commands.length →
      tables literal offset matched = .ok codes → ReverseBits.StartWire stream cursor →
      CommandsWire codes cursor.bits commands →
      SectionWire (encoded ++ [0x54, literal, offset, matched] ++ stream) commands

namespace Internal

def readCommand (codes : Codes) (cursor : ReverseBits.Cursor) :
    Option (Sequence.Command × ReverseBits.Cursor) := do
  let (offset, cursor) ← ReverseBits.read codes.offset.width cursor
  let (matched, cursor) ← ReverseBits.read codes.matched.width cursor
  let (literals, cursor) ← ReverseBits.read codes.literals.width cursor
  return (⟨codes.literals.base + literals, codes.offset.base + offset, codes.matched.base + matched⟩,
    cursor)

def readCommands (codes : Codes) : Nat → ReverseBits.Cursor → List Sequence.Command →
    Except Error (List Sequence.Command)
  | 0, cursor, acc => if cursor.isEmpty then .ok acc.reverse else .error .trailingBits
  | count + 1, cursor, acc =>
    match readCommand codes cursor with
    | none => .error .bitUnderflow
    | some (command, rest) => readCommands codes count rest (command :: acc)

def readRle (count : Nat) : List UInt8 → Except Error (List Sequence.Command)
  | mode :: body => do
    if mode.toNat % 4 ≠ 0 then throw .reservedModeBits
    if mode ≠ 0x54 then throw (.unsupportedModes mode)
    let literal :: offset :: matched :: stream := body | throw .truncated
    let codes ← tables literal offset matched
    let some cursor := ReverseBits.start stream | throw .badEndMarker
    readCommands codes count cursor []
  | [] => .error .truncated

end Internal

/-- Decode one exact section, checking both caller caps before reading tables
    or producing commands. Non-RLE mode combinations are explicit errors. -/
def decode (limits : Limits) (input : List UInt8) : Except Error (List Sequence.Command) := do
  if limits.inputCapacity < input.length then throw .inputLimit
  let (count, rest) ← (LiteralBlock.readSequenceCount input).mapError (fun _ => Error.truncated)
  if limits.commands < count then throw .commandLimit
  if count = 0 then
    if rest.isEmpty then .ok [] else .error .trailingInput
  else Internal.readRle count rest

end Silmaril.Formats.Compression.Zstd.RleSequences
