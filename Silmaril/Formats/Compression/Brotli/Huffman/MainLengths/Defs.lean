module

public import Silmaril.Formats.Compression.Brotli.Huffman.CodeLengthSymbol.Defs

/-! # Brotli main code lengths

RFC 7932 §3.5 with a previously checked code-length table. Return a
full alphabet in order, including the implicit trailing zeros.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Huffman.MainLengths

structure Limits where
  alphabet : Nat
  bits : Nat
  deriving Repr

inductive Error where
  | alphabetSize
  | alphabetLimit
  | symbol (reason : CodeLengthSymbol.Error)
  | bitLimit
  | truncated
  | repeatExtent
  | oversubscribed
  | incomplete
  deriving DecidableEq, Repr

inductive RepeatKind where
  | previous | zero
  deriving DecidableEq, Repr

def RepeatKind.symbol : RepeatKind → Nat
  | .previous => 16
  | .zero => 17

def RepeatKind.width : RepeatKind → Nat
  | .previous => 2
  | .zero => 3

/-- A zero old count starts a run. Repeating the same token extends the
    prior run to the newly computed total. -/
def RepeatKind.total (kind : RepeatKind) (old extra : Nat) : Nat :=
  if old = 0 then 3 + extra else 2 ^ kind.width * (old - 2) + (3 + extra)

structure History where
  prior : Fin 16
  previousRun : Option (RepeatKind × Nat)

def History.start : History := ⟨8, none⟩

def History.Valid (history : History) : Prop :=
  match history.previousRun with
  | none => True
  | some (_, count) => 3 ≤ count

def History.continued (history : History) (kind : RepeatKind) : Nat :=
  match history.previousRun with
  | some (last, count) => if last = kind then count else 0
  | none => 0

inductive Token where
  | length (value : Fin 16)
  | repeat (kind : RepeatKind) (extra : Nat)

structure Run where
  value : Fin 16
  count : Nat
  next : History

/-- Each repeat emits only the additional lengths contributed by its
    new total. The previous nonzero length survives zero lengths. -/
def Token.emit (token : Token) (history : History) : Run :=
  match token with
  | .length value =>
    ⟨value, 1, ⟨if value = 0 then history.prior else value, none⟩⟩
  | .repeat kind extra =>
    let old := history.continued kind
    let total := kind.total old extra
    let value := if kind = .previous then history.prior else 0
    ⟨value, total - old, ⟨history.prior, some (kind, total)⟩⟩

def mass (value : Nat) : Nat :=
  if value = 0 then 0 else 32768 >>> value

def kraft (lengths : List Nat) : Nat := (lengths.map mass).sum

inductive TokenWire (table : CodeLengths.Table) : Token → List Bool → Prop where
  | length {value : Fin 16} {bits : List Bool} :
      CodeLengthSymbol.Wire table value.val bits → TokenWire table (.length value) bits
  | run {kind : RepeatKind} {extra : Nat} {bits : List Bool} :
      CodeLengthSymbol.Wire table kind.symbol bits → extra < 2 ^ kind.width →
      TokenWire table (.repeat kind extra) (bits ++ natBits extra kind.width)

/-- The ordered wire trace stops at exact Kraft exhaustion. The
    remaining alphabet slots are represented by implicit zero lengths. -/
inductive RunsWire (table : CodeLengths.Table) :
    History → Nat → Nat → List Bool → List Nat → Prop where
  | done (history : History) (slots : Nat) :
      RunsWire table history slots 0 [] (List.replicate slots 0)
  | step {history : History} {slots space : Nat} {token : Token}
      {tokenBits tailBits : List Bool} {tail : List Nat} {run : Run} :
      token.emit history = run → history.Valid →
      0 < space → 0 < run.count → run.count ≤ slots → run.count * mass run.value.val ≤ space →
      TokenWire table token tokenBits →
      RunsWire table run.next (slots - run.count) (space - run.count * mass run.value.val) tailBits tail →
      RunsWire table history slots space (tokenBits ++ tailBits)
        (List.replicate run.count run.value.val ++ tail)

namespace Internal

structure Cursor where
  reader : LSBReader
  remaining : Nat

def readRepeat (kind : RepeatKind) (cursor : Cursor) : Except Error (Token × Cursor) :=
  if cursor.remaining < kind.width then .error .bitLimit
  else
    match cursor.reader.readBits kind.width with
    | none => .error .truncated
    | some (extra, after) => .ok (.repeat kind extra, ⟨after, cursor.remaining - kind.width⟩)

def readToken (table : CodeLengths.Table) (cursor : Cursor) : Except Error (Token × Cursor) := do
  let (symbol, after) ← (CodeLengthSymbol.read table cursor.remaining cursor.reader).mapError Error.symbol
  let next : Cursor := ⟨after, cursor.remaining - (after.totalRead - cursor.reader.totalRead)⟩
  if regular : symbol < 16 then
    pure (.length ⟨symbol, regular⟩, next)
  else
    readRepeat (if symbol = 16 then .previous else .zero) next

/-- The fuel is the alphabet size. An accepted step emits at least one
    length even when the prefix code itself uses no bits. -/
def expand (table : CodeLengths.Table) : Nat → Nat → Nat → History → Cursor →
    Except Error (List Nat × Cursor)
  | fuel, slots, space, history, cursor =>
    if space = 0 then .ok (List.replicate slots 0, cursor)
    else
      match fuel with
      | 0 => .error .incomplete
      | fuel + 1 =>
        if slots = 0 then .error .incomplete
        else do
          let (token, after) ← readToken table cursor
          let run := token.emit history
          let cost := run.count * mass run.value.val
          if slots < run.count then .error .repeatExtent
          else if space < cost then .error .oversubscribed
          else
            let (tail, last) ← expand table fuel (slots - run.count) (space - cost) run.next after
            pure (List.replicate run.count run.value.val ++ tail, last)

end Internal

/-- Read the main lengths for a standard RFC alphabet of at most 704
    symbols, under the caller's alphabet and bit budgets. -/
def read (limits : Limits) (alphabet : Nat) (table : CodeLengths.Table) (reader : LSBReader) :
    Except Error (List Nat × LSBReader) :=
  if alphabet = 0 ∨ 704 < alphabet then .error .alphabetSize
  else if limits.alphabet < alphabet then .error .alphabetLimit
  else do
    let (lengths, after) ← Internal.expand table alphabet alphabet 32768 History.start ⟨reader, limits.bits⟩
    pure (lengths, after.reader)

end Silmaril.Formats.Compression.Brotli.Huffman.MainLengths
