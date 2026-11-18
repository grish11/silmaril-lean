module

public import Init.Data.ByteArray

/-! # Cursor parser and exact-consumption grammar core -/

@[expose] public section

namespace Silmaril.Parse.ByteParse

/-- What went wrong. Constant payloads only: building an error allocates
nothing beyond the error itself, and only on failure. -/
inductive Kind where
  /-- The window ended. -/
  | eof
  /-- An unexpected tag byte for the named production. -/
  | tag (what : String) (byte : UInt8)
  /-- A LEB128 number is too long or out of range. -/
  | leb
  /-- A vector count exceeds the bytes left in the window. -/
  | count (n : Nat)
  /-- A name is not UTF-8. -/
  | utf8
  /-- A sub-parser did not consume its sized window exactly. -/
  | size (expected consumed : Nat)
  /-- Bytes remain where the input should end. -/
  | trailing
  /-- A loop body made no progress. -/
  | stuck
  /-- A recursion depth bound was exhausted. -/
  | depth
  /-- Any other message (cold path only). -/
  | other (msg : String)
  deriving Repr, Inhabited, BEq

/-- An error and the position where it was detected. -/
structure Error where
  pos : Nat
  kind : Kind
  deriving Repr, Inhabited, BEq

/-- The result of a parser: a value and the next position, or an error. -/
inductive Res (α : Type) where
  | ok (a : α) (pos : Nat)
  | err (e : Error)
  deriving Repr, Inhabited

/-- A parser: input, window end, position. -/
def Parser (α : Type) : Type := ByteArray → Nat → Nat → Res α

namespace Parser

@[inline] protected def pure {α : Type} (a : α) : Parser α := fun _ _ i => .ok a i

@[inline] protected def bind {α β : Type} (p : Parser α) (f : α → Parser β) : Parser β :=
  fun bs s i =>
    match p bs s i with
    | .ok a j => f a bs s j
    | .err e => .err e

@[inline] protected def map {α β : Type} (f : α → β) (p : Parser α) : Parser β :=
  fun bs s i =>
    match p bs s i with
    | .ok a j => .ok (f a) j
    | .err e => .err e

instance : Monad Parser where
  pure := Parser.pure
  bind := Parser.bind
  map := Parser.map

end Parser

/-- Fail with `k` at the current position. -/
@[inline] def fail {α : Type} (k : Kind) : Parser α := fun _ _ i => .err ⟨i, k⟩

/-- One byte. -/
@[inline] def byte : Parser UInt8 := fun bs s i =>
  if hs : i < s then
    if h : i < bs.size then .ok bs[i] (i + 1) else .err ⟨i, .eof⟩
  else .err ⟨i, .eof⟩

/-! ## Specifications -/

/-- Byte lists, the reference representation used by grammars. -/
abbrev Bytes := List UInt8

/-- The bytes of `bs` from `i` to `j`. -/
abbrev seg (bs : ByteArray) (i j : Nat) : Bytes := bs.data.toList.extract i j

/-- `p` is sound for the grammar `G`: started inside a window that lies inside
the input, a successful run does not move backward, stays in the window, and `G`
relates the consumed bytes to the result. -/
def Sound {α : Type} (G : Bytes → α → Prop) (p : Parser α) : Prop :=
  ∀ ⦃bs : ByteArray⦄ ⦃st i : Nat⦄ ⦃a : α⦄ ⦃j : Nat⦄, i ≤ st → st ≤ bs.size →
    p bs st i = .ok a j → i ≤ j ∧ j ≤ st ∧ G (seg bs i j) a

/-- `p` is complete for `G`: if its window begins with `l` and `G l a`, it
answers `a` after exactly `l`. Implies that `G` is unambiguous on prefixes. -/
def Complete {α : Type} (G : Bytes → α → Prop) (p : Parser α) : Prop :=
  ∀ ⦃l : Bytes⦄ ⦃a : α⦄ ⦃bs : ByteArray⦄ ⦃st i : Nat⦄, G l a →
    i + l.length ≤ st → st ≤ bs.size → seg bs i (i + l.length) = l →
    p bs st i = .ok a (i + l.length)

/-- `G` never relates the empty string (what `vec` and `untilEnd` need). -/
def NonEmpty {α : Type} (G : Bytes → α → Prop) : Prop := ∀ ⦃l a⦄, G l a → l ≠ []

/-! ## Grammar combinators (relations) -/

namespace Spec

/-- Concatenation, with the second part depending on the first value. -/
def bind {α β : Type} (G : Bytes → α → Prop) (H : α → Bytes → β → Prop) : Bytes → β → Prop :=
  fun l b => ∃ l₁ l₂ a, l = l₁ ++ l₂ ∧ G l₁ a ∧ H a l₂ b

/-- The image of a grammar. -/
def map {α β : Type} (f : α → β) (G : Bytes → α → Prop) : Bytes → β → Prop :=
  fun l b => ∃ a, G l a ∧ f a = b

/-- Exactly the empty string. -/
def pure {α : Type} (a : α) : Bytes → α → Prop := fun l b => l = [] ∧ b = a

end Spec

/-- Exactly one byte. -/
def Spec.byte : Bytes → UInt8 → Prop := fun l b => l = [b]

/-- A parser that is complete when its window ends exactly after the encoding. -/
def CompleteAtEnd {α : Type} (G : Bytes → α → Prop) (p : Parser α) : Prop :=
  ∀ ⦃l : Bytes⦄ ⦃a : α⦄ ⦃bs : ByteArray⦄ ⦃i : Nat⦄, G l a →
    i + l.length ≤ bs.size → seg bs i (i + l.length) = l → p bs (i + l.length) i = .ok a (i + l.length)

/-! ## Grammars -/

/-- A parser with the grammar it implements. -/
structure Grammar (α : Type) where
  /-- The relation between consumed bytes and values. -/
  G : Bytes → α → Prop
  /-- The executable parser. -/
  parse : Parser α

/-- The parser of `g` is sound and complete for its grammar. -/
class Grammar.Lawful {α : Type} (g : Grammar α) : Prop where
  sound : Sound g.G g.parse
  complete : Complete g.G g.parse

/-- A parser with its grammar, meant to be complete up to the end of its window. -/
structure GrammarE (α : Type) where
  /-- The relation between consumed bytes and values. -/
  G : Bytes → α → Prop
  /-- The executable parser. -/
  parse : Parser α

/-- The parser of `g` is sound, and complete when its window ends after the encoding. -/
class GrammarE.Lawful {α : Type} (g : GrammarE α) : Prop where
  sound : Sound g.G g.parse
  complete : CompleteAtEnd g.G g.parse

namespace Grammar

variable {α β : Type}

@[inline] def pure (a : α) : Grammar α := ⟨Spec.pure a, Pure.pure a⟩

@[inline] def bind (g : Grammar α) (h : α → Grammar β) : Grammar β :=
  ⟨Spec.bind g.G (fun a => (h a).G), g.parse >>= fun a => (h a).parse⟩

@[inline] def map (f : α → β) (g : Grammar α) : Grammar β :=
  ⟨Spec.map f g.G, Parser.map f g.parse⟩

@[inline] def byte : Grammar UInt8 := ⟨Spec.byte, ByteParse.byte⟩

end Grammar

end Silmaril.Parse.ByteParse
