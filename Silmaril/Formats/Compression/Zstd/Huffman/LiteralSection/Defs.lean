module

public import Silmaril.Formats.Compression.XxHash.Defs
public import Silmaril.Formats.Compression.Zstd.Huffman.FourStream.Defs
public import Silmaril.Formats.Compression.Zstd.Huffman.TreeDescription.Defs

/-! # Zstandard new-tree compressed literal sections

RFC 8878 §§3.1.1.3.1.1 and 3.1.1.3.1.4–6. The input starts at a type-2
literal header. The reader returns its decoded literals and the following
bytes verbatim.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection

inductive SizeFormat where
  | one10
  | four10
  | four14
  | four18
  deriving DecidableEq, Repr

def SizeFormat.decode : Nat → SizeFormat
  | 0 => .one10
  | 1 => .four10
  | 2 => .four14
  | _ => .four18

def SizeFormat.code : SizeFormat → Nat
  | .one10 => 0
  | .four10 => 1
  | .four14 => 2
  | .four18 => 3

def SizeFormat.headerBytes : SizeFormat → Nat
  | .one10 | .four10 => 3
  | .four14 => 4
  | .four18 => 5

def SizeFormat.fieldBits : SizeFormat → Nat
  | .one10 | .four10 => 10
  | .four14 => 14
  | .four18 => 18

structure Header where
  format : SizeFormat
  regenerated : Nat
  compressed : Nat
  deriving DecidableEq, Repr

structure Limits where
  inputBytes : Nat
  outputBytes : Nat
  tree : TreeDescription.Limits
  deriving DecidableEq, Repr

/-- Counts the literal header and its declared compressed payload. -/
def Limits.inputCap (limits : Limits) : Nat := min limits.inputBytes 131072

def Limits.outputCap (limits : Limits) : Nat := min limits.outputBytes 131072

structure Prefix where
  header : Header
  literals : List UInt8
  consumed : Nat
  rest : List UInt8
  deriving DecidableEq, Repr

inductive Unsupported where
  | raw
  | rle
  | treeless
  deriving DecidableEq, Repr

inductive Error where
  | truncatedHeader
  | truncatedBody
  | unsupported (feature : Unsupported)
  | inputLimit
  | outputLimit
  | tree (reason : TreeDescription.Error)
  | single (reason : SingleStream.Error)
  | four (reason : FourStream.Error)
  deriving DecidableEq, Repr

def Header.WireFor (header : Header) (kind : Nat) (bytes : List UInt8) : Prop :=
  ∃ first tail, bytes = first :: tail ∧ first.toNat % 4 = kind ∧
    first.toNat / 4 % 4 = header.format.code ∧ bytes.length = header.format.headerBytes ∧
    header.regenerated = XxHash.leNat bytes / 16 % 2 ^ header.format.fieldBits ∧
    header.compressed = XxHash.leNat bytes / 2 ^ (4 + header.format.fieldBits)

def Header.Wire (header : Header) (bytes : List UInt8) : Prop := header.WireFor 2 bytes

def Header.extent (header : Header) : Nat := header.format.headerBytes + header.compressed

structure Envelope where
  header : Header
  body : List UInt8
  rest : List UInt8

def Envelope.Wire (envelope : Envelope) (kind : Nat) (input : List UInt8) : Prop :=
  ∃ bytes, input = bytes ++ (envelope.body ++ envelope.rest) ∧
    envelope.header.WireFor kind bytes ∧ envelope.body.length = envelope.header.compressed

def StreamsWire (header : Header) (table : SingleStream.Table) (declared : Nat)
    (input out : List UInt8) : Prop :=
  if header.format = .one10 then FourStream.ChunkWire table ⟨input, header.regenerated⟩ out
  else FourStream.DecodedWire table declared header.regenerated input out

def Wire (limits : Limits) (input : List UInt8) (result : Prefix) : Prop :=
  ∃ (headerBytes body : List UInt8) (tree : TreeDescription.Prefix) (table : SingleStream.Table),
    input = headerBytes ++ (body ++ result.rest) ∧ result.header.Wire headerBytes ∧
    body.length = result.header.compressed ∧ result.consumed = headerBytes.length + body.length ∧
    tree.Valid limits.tree body ∧ SingleStream.TableWire tree.tree table ∧
    tree.rest.length = result.header.compressed - tree.consumed ∧
    StreamsWire result.header table (result.header.compressed - tree.consumed) tree.rest result.literals

namespace Internal

def readFields (first : UInt8) (rest : List UInt8) : Except Error (Header × List UInt8) :=
  let format := SizeFormat.decode (first.toNat / 4 % 4)
  let size := format.headerBytes - 1
  let tail := rest.take size
  if tail.length ≠ size then .error .truncatedHeader
  else
    let bits := XxHash.leNat (first :: tail)
    .ok (⟨format, bits / 16 % 2 ^ format.fieldBits, bits / 2 ^ (4 + format.fieldBits)⟩, rest.drop size)

def cutEnvelope (limits : Limits) (header : Header) (body : List UInt8) : Except Error Envelope :=
  if limits.inputCap < header.extent then .error .inputLimit
  else if limits.outputCap < header.regenerated then .error .outputLimit
  else
    let compressed := body.take header.compressed
    if compressed.length ≠ header.compressed then .error .truncatedBody
    else .ok ⟨header, compressed, body.drop header.compressed⟩

def readStreams (limits : Limits) (header : Header) (declared : Nat) (input : List UInt8)
    (table : SingleStream.Table) : Except Error (List UInt8) :=
  if header.format = .one10 then
    (SingleStream.Internal.readStream table header.regenerated input).mapError Error.single
  else
    (FourStream.decodeTable ⟨limits.inputCap, limits.outputCap⟩ table declared header.regenerated input).mapError
      Error.four

end Internal

/-- Read all and only the bytes of the new-tree header. -/
def readHeader : List UInt8 → Except Error (Header × List UInt8)
  | [] => .error .truncatedHeader
  | first :: rest =>
    let kind := first.toNat % 4
    if kind = 2 then Internal.readFields first rest
    else .error (.unsupported (if kind = 0 then .raw else if kind = 1 then .rle else .treeless))

/-- Apply both size caps before slicing the exact payload. The tree and
    streams use that slice, leaving the following bytes untouched. -/
def read (limits : Limits) (input : List UInt8) : Except Error Prefix := do
  let (header, body) ← readHeader input
  let envelope ← Internal.cutEnvelope limits header body
  let (tree, table) ← (TreeDescription.readTable limits.tree envelope.body).mapError Error.tree
  let literals ← Internal.readStreams limits header (header.compressed - tree.consumed) tree.rest table
  return ⟨header, literals, header.extent, envelope.rest⟩

end Silmaril.Formats.Compression.Zstd.Huffman.LiteralSection
