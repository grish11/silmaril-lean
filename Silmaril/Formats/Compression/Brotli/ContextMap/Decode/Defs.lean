module

public import Silmaril.Formats.Compression.Brotli.ContextMap.Defs

/-! Complete literal or distance context maps (RFC 7932 §7.3).
The count, description, map symbols, run extras and IMTF flag use
one bit cap. Each coded symbol uses a work unit and emits entries. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.ContextMap.Decode

structure Limits where
  /-- Maximum number of expanded entries. -/
  entries : Nat
  /-- Maximum number of coded map symbols, including zero-width symbols. -/
  symbols : Nat
  /-- Maximum committed bits from the count through the optional IMTF flag. -/
  bits : Nat

inductive Error where
  | prefixError (reason : ContextMap.Error)
  | symbol (reason : Huffman.Description.SymbolError)
  | bitLimit
  | truncated
  | symbolLimit
  | indexRange
  | runExtent
  | unusedTree
  deriving DecidableEq, Repr

inductive Map where
  | implicit (entries : Nat)
  | coded (trees : Nat) (values : List Nat)
  deriving DecidableEq, Repr

def Map.treeCount : Map → Nat
  | .implicit _ => 1
  | .coded trees _ => trees

def Map.indices : Map → List Nat
  | .implicit entries => List.replicate entries 0
  | .coded _ values => values

/-- A single zero has width zero and consumes no extra field. -/
def runWidth (rleMax symbol : Nat) : Nat :=
  if 0 < symbol ∧ symbol ≤ rleMax then symbol else 0

inductive RunWire (trees rleMax : Nat) (table : Huffman.Description.Table) :
    List Bool → Nat → Nat → Prop where
  | emit {symbol code width extra : Nat} :
      symbol < trees + rleMax → table.codeFor symbol = some (code, width) → width ≤ 15 →
      extra < 2 ^ runWidth rleMax symbol →
      RunWire trees rleMax table (msbBits code width ++ natBits extra (runWidth rleMax symbol))
        (symbol - rleMax) (2 ^ runWidth rleMax symbol + extra)

inductive RunsWire (trees rleMax : Nat) (table : Huffman.Description.Table) :
    Nat → Nat → List Bool → List Nat → Prop where
  | done : RunsWire trees rleMax table 0 0 [] []
  | step {slots work value count : Nat} {bits tailBits : List Bool} {tail : List Nat} :
      count ≤ slots → RunWire trees rleMax table bits value count →
      RunsWire trees rleMax table (slots - count) work tailBits tail →
      RunsWire trees rleMax table slots (work + 1) (bits ++ tailBits)
        (List.replicate count value ++ tail)

/-- At each step take the indexed value out of the current list and
    put it at the front. The initial list contains all tree indices. -/
inductive MtfWire : List Nat → List Nat → List Nat → Prop where
  | done (order : List Nat) : MtfWire order [] []
  | step {order positions values : List Nat} {position value : Nat} :
      order[position]? = some value →
      MtfWire (value :: order.eraseIdx position) positions values →
      MtfWire order (position :: positions) (value :: values)

inductive TransformWire (trees : Nat) : Bool → List Nat → List Nat → Prop where
  | identity (values : List Nat) : TransformWire trees false values values
  | inverse {positions values : List Nat} :
      MtfWire (List.range trees) positions values → TransformWire trees true positions values

inductive Wire (entries : Nat) : Nat → List Bool → Map → Prop where
  | implicit : 0 < entries → Wire entries 0 [false] (.implicit entries)
  | coded {trees rleMax work : Nat} {table : Huffman.Description.Table}
      {header body : List Bool} {flag : Bool} {positions values : List Nat} :
      ContextMap.Wire entries header (.coded entries trees rleMax table) →
      RunsWire trees rleMax table entries work body positions →
      TransformWire trees flag positions values →
      (∀ index, index < trees → index ∈ values) →
      Wire entries work (header ++ body ++ [flag]) (.coded trees values)

namespace Internal

structure Cursor where
  reader : LSBReader
  remaining : Nat

def Cursor.advance (cursor : Cursor) (after : LSBReader) : Cursor :=
  ⟨after, cursor.remaining - (after.totalRead - cursor.reader.totalRead)⟩

def take (cursor : Cursor) (width : Nat) : Except Error (Nat × Cursor) :=
  if cursor.remaining < width then .error .bitLimit
  else
    match cursor.reader.readBits width with
    | none => .error .truncated
    | some (value, after) => .ok (value, ⟨after, cursor.remaining - width⟩)

def readRun (trees rleMax : Nat) (table : Huffman.Description.Table) (cursor : Cursor) :
    Except Error (Nat × Nat × Cursor) := do
  let (symbol, after) ← (table.readBounded cursor.remaining cursor.reader).mapError Error.symbol
  if trees + rleMax ≤ symbol then throw .indexRange
  else
    let width := runWidth rleMax symbol
    let (extra, next) ← take (cursor.advance after) width
    pure (symbol - rleMax, 2 ^ width + extra, next)

/-- Stop on the exact entry boundary, including when the symbol table
    has a zero-bit singleton. Debit slots before materializing a run. -/
def expand (trees rleMax : Nat) (table : Huffman.Description.Table) :
    Nat → Nat → Cursor → Except Error (List Nat × Cursor)
  | fuel, slots, cursor =>
    if slots = 0 then pure ([], cursor)
    else
      match fuel with
      | 0 => throw .symbolLimit
      | fuel + 1 => do
        let (value, count, next) ← readRun trees rleMax table cursor
        if slots < count then throw .runExtent
        else
          let (tail, after) ← expand trees rleMax table fuel (slots - count) next
          pure (List.replicate count value ++ tail, after)

def inverseMtf (order : List Nat) : List Nat → Except Error (List Nat)
  | [] => .ok []
  | position :: positions => do
    let some value := order[position]? | throw .indexRange
    let values ← inverseMtf (value :: order.eraseIdx position) positions
    pure (value :: values)

def transform (trees : Nat) (flag : Bool) (positions : List Nat) : Except Error (List Nat) :=
  if flag then inverseMtf (List.range trees) positions else .ok positions

def finish (trees : Nat) (flag : Bool) (positions : List Nat) : Except Error Map := do
  let values ← transform trees flag positions
  if (List.range trees).all (fun index => values.contains index) then pure (.coded trees values)
  else throw .unusedTree

def readCoded (entries trees rleMax : Nat) (table : Huffman.Description.Table)
    (symbols : Nat) (cursor : Cursor) : Except Error (Map × LSBReader) := do
  let (positions, next) ← expand trees rleMax table (min entries symbols) entries cursor
  let (flag, after) ← take next 1
  let result ← finish trees (flag ≠ 0) positions
  pure (result, after.reader)

end Internal

/-- Read the complete map at NTREES, leaving the next header field
    untouched. Implicit maps need no symbol work or IMTF flag. -/
def read (kind : Kind) (types : Nat) (limits : Limits) (before : LSBReader) :
    Except Error (Map × LSBReader) := do
  let (header, after) ← (ContextMap.read kind types ⟨limits.entries, limits.bits⟩ before).mapError Error.prefixError
  match header with
  | .implicit entries => pure (.implicit entries, after)
  | .coded entries trees rleMax table =>
    let cursor : Internal.Cursor := ⟨before, limits.bits⟩
    Internal.readCoded entries trees rleMax table limits.symbols (cursor.advance after)

end Silmaril.Formats.Compression.Brotli.ContextMap.Decode
