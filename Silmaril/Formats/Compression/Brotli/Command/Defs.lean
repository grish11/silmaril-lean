module

public import Silmaril.Formats.Compression.Brotli.CompressedHeader.Defs
import Init.Omega

/-! RFC 7932 §5. Read a command symbol, followed by its little-endian
insert and copy extras. The result stops before the literals and any
subsequent distance field. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Command

open Huffman.Description (Table)

/-- Whether a subsequent copy uses implicit distance code zero or
    reads a distance code. A final literal-only command can end first. -/
inductive DistanceMode where
  | implicitZero
  | explicit
  deriving DecidableEq, Repr

structure LengthCode where
  base : Nat
  extraBits : Nat
  deriving DecidableEq, Repr

def LengthCode.last (code : LengthCode) : Nat := code.base + 2 ^ code.extraBits - 1

/-- The lower endpoint and extra-bit width of each RFC insert length code. -/
def insertCodes : Vector LengthCode 24 := #v[
  ⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨4, 0⟩, ⟨5, 0⟩, ⟨6, 1⟩, ⟨8, 1⟩,
  ⟨10, 2⟩, ⟨14, 2⟩, ⟨18, 3⟩, ⟨26, 3⟩, ⟨34, 4⟩, ⟨50, 4⟩, ⟨66, 5⟩, ⟨98, 5⟩,
  ⟨130, 6⟩, ⟨194, 7⟩, ⟨322, 8⟩, ⟨578, 9⟩, ⟨1090, 10⟩, ⟨2114, 12⟩, ⟨6210, 14⟩, ⟨22594, 24⟩]

/-- The lower endpoint and extra-bit width of each RFC copy length code. -/
def copyCodes : Vector LengthCode 24 := #v[
  ⟨2, 0⟩, ⟨3, 0⟩, ⟨4, 0⟩, ⟨5, 0⟩, ⟨6, 0⟩, ⟨7, 0⟩, ⟨8, 0⟩, ⟨9, 0⟩,
  ⟨10, 1⟩, ⟨12, 1⟩, ⟨14, 2⟩, ⟨18, 2⟩, ⟨22, 3⟩, ⟨30, 3⟩, ⟨38, 4⟩, ⟨54, 4⟩,
  ⟨70, 5⟩, ⟨102, 5⟩, ⟨134, 6⟩, ⟨198, 7⟩, ⟨326, 8⟩, ⟨582, 9⟩, ⟨1094, 10⟩, ⟨2118, 24⟩]

/-- (Insert row, copy column) in increasing order of the RFC's
    eleven 64-symbol cells. The first two cells imply distance code zero. -/
def cells : Vector (Fin 3 × Fin 3) 11 :=
  #v[(0, 0), (0, 1), (0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (2, 0), (1, 2), (2, 1), (2, 2)]

def lengthIndices (symbol : Fin 704) : Fin 24 × Fin 24 :=
  let cell := cells[symbol.val / 64]'(by have := symbol.isLt; omega)
  let insert := symbol.val / 8 % 8
  let copy := symbol.val % 8
  ⟨⟨8 * cell.1.val + insert, by have := cell.1.isLt; omega⟩,
    ⟨8 * cell.2.val + copy, by have := cell.2.isLt; omega⟩⟩

structure Spec where
  insert : LengthCode
  copy : LengthCode
  distance : DistanceMode
  deriving DecidableEq, Repr

/-- A total RFC lookup over all 704 command ordinals. -/
def spec (symbol : Fin 704) : Spec :=
  let (insert, copy) := lengthIndices symbol
  ⟨insertCodes[insert.val], copyCodes[copy.val],
    if symbol.val < 128 then .implicitZero else .explicit⟩

structure Value where
  symbol : Fin 704
  insertLength : Nat
  copyLength : Nat
  distance : DistanceMode
  deriving DecidableEq, Repr

def value (symbol : Fin 704) (insertExtra copyExtra : Nat) : Value :=
  let fields := spec symbol
  ⟨symbol, fields.insert.base + insertExtra, fields.copy.base + copyExtra, fields.distance⟩

inductive Field where
  | insertExtra | copyExtra
  deriving DecidableEq, Repr

inductive Error where
  | alphabet
  | symbol (reason : Huffman.Description.SymbolError)
  | symbolRange
  | bitLimit (field : Field)
  | truncated (field : Field)
  | commandBlockTypes
  | commandTreeGroup
  deriving DecidableEq, Repr

/-- The original extra fields occur in insert-then-copy order. -/
inductive ExtrasWire (symbol : Fin 704) : List Bool → Value → Prop where
  | fields {insertExtra copyExtra : Nat} :
      insertExtra < 2 ^ (spec symbol).insert.extraBits →
      copyExtra < 2 ^ (spec symbol).copy.extraBits →
      ExtrasWire symbol (natBits insertExtra (spec symbol).insert.extraBits ++
        natBits copyExtra (spec symbol).copy.extraBits) (value symbol insertExtra copyExtra)

inductive Wire (table : Table) : List Bool → Value → Prop where
  | command {command : Value} {code width : Nat} {extras : List Bool} :
      table.alphabetSize = 704 →
      table.codeFor command.symbol.val = some (code, width) →
      width ≤ 15 → ExtrasWire command.symbol extras command →
      Wire table (msbBits code width ++ extras) command

namespace Internal

def take (field : Field) (limit width : Nat) (before : LSBReader) : Except Error (Nat × LSBReader) :=
  if limit < width then .error (.bitLimit field)
  else
    match before.readBits width with
    | none => .error (.truncated field)
    | some result => .ok result

end Internal

/-- Read only the extra fields when the command symbol is already known. -/
def readExtras (symbol : Fin 704) (bitLimit : Nat) (before : LSBReader) :
    Except Error (Value × LSBReader) := do
  let fields := spec symbol
  let (insertExtra, cursor) ← Internal.take .insertExtra bitLimit fields.insert.extraBits before
  let (copyExtra, after) ←
    Internal.take .copyExtra (bitLimit - fields.insert.extraBits) fields.copy.extraBits cursor
  pure (value symbol insertExtra copyExtra, after)

/-- Read one command from the selected command tree under a shared bit cap. -/
def read (table : Table) (bitLimit : Nat) (before : LSBReader) : Except Error (Value × LSBReader) := do
  if table.alphabetSize ≠ 704 then throw .alphabet
  else
    let (symbol, after) ← (table.readBounded bitLimit before).mapError Error.symbol
    if bounded : symbol < 704 then
      readExtras ⟨symbol, bounded⟩ (bitLimit - (after.totalRead - before.totalRead)) after
    else throw .symbolRange

/-- For one command block type, use the sole tree in the checked header.
    The caller supplies the cursor at a command boundary. -/
def readSingle (header : CompressedHeader.Header) (bitLimit : Nat) (before : LSBReader) :
    Except Error (Value × LSBReader) :=
  match header.initial.controls.insertCopy with
  | .multiple .. => .error .commandBlockTypes
  | .single =>
    match header.insertCopyTrees with
    | [table] => read table bitLimit before
    | _ => .error .commandTreeGroup

end Silmaril.Formats.Compression.Brotli.Command
