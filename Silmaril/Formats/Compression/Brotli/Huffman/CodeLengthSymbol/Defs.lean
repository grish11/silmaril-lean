module

public import Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths.Defs

/-! A bounded read of one symbol from the checked Brotli code-length table. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Huffman.CodeLengthSymbol

inductive Error where
  | bitLimit
  | truncated
  | invalidCode
  deriving DecidableEq, Repr

/-- The checked table assigns the symbol these incoming bits. -/
def Wire (table : CodeLengths.Table) (symbol : Nat) (bits : List Bool) : Prop :=
  symbol < 18 ∧ ∃ code width, table.codeFor symbol = some (code, width) ∧
    width ≤ 5 ∧ bits = msbBits code width

namespace Internal

/-- A depth-five code can use at most the buffered suffix and one more byte. -/
def lookWidth (limit : Nat) (reader : LSBReader) : Nat :=
  min (min limit 5) (reader.count + if reader.input.isEmpty then 0 else 8)

/-- Check the reported code against the original cursor. This commits
    only the symbol's width, regardless of the lookahead used to find it. -/
def commit (table : CodeLengths.Table) (widthLimit symbol : Nat) (reader : LSBReader) :
    Except Error (Nat × LSBReader) :=
  if 18 ≤ symbol then .error .invalidCode
  else
    match table.codeFor symbol with
    | none => .error .invalidCode
    | some (code, width) =>
      if widthLimit < width then .error .invalidCode
      else
        match reader.readBits width with
        | none => .error .truncated
        | some (value, after) =>
          if natBits value width = msbBits code width then .ok (symbol, after)
          else .error .invalidCode

end Internal

/-- Read one symbol. The shared canonical Huffman decoder runs on a
    scratch cursor containing only the bounded lookahead. -/
def read (table : CodeLengths.Table) (limit : Nat) (reader : LSBReader) :
    Except Error (Nat × LSBReader) := do
  match table.codes with
  | .singleton symbol => pure (symbol, reader)
  | .canonical canonical =>
    let width := Internal.lookWidth limit reader
    let some (bits, _) := reader.readBits width | throw .truncated
    let some (symbol, _) := canonical.readSymbolLSB ⟨bits, width, [], 0⟩
      | throw (if width = 5 then .invalidCode else if width = limit then .bitLimit else .truncated)
    Internal.commit table width symbol reader

end Silmaril.Formats.Compression.Brotli.Huffman.CodeLengthSymbol
