module

public import Silmaril.Formats.SExp.Tagged
public import Silmaril.Formats.Spki.Defs

/-!
# Tree families: atom signatures and tagged ASTs with typed payloads

Named S-expression families, tagged ASTs with typed payloads, and the dotted/proper
roundtrip. All
reuse the existing tree types: proper S-expressions `SExp α`, dotted ones `SExp2 α`, binary
trees `Tree2 α` and tagged expressions `TExpr τ α` (`Silmaril.Formats.SExp.{Basic,Proper,Tagged}`);
this file adds no new recursive tree type.

## Atom families (first-class S-expression APIs)

An S-expression family is `SExp α` for an atom type `α`. The named families are:

| family | atoms |
| --- | --- |
| `SymbolSExp` | `String` |
| `ByteSExp` | `List UInt8` |
| `WordSExp` | `BitVec 64` (an `i64`) |
| `SymStrSExp` | symbols, strings |
| `SymBytesSExp` | symbols, byte strings |
| `SymStrBytesSExp` | symbols, strings, byte strings |
| `SymStrKwSExp` | symbols, strings, keywords |
| `SymStrKwBytesSExp` | symbols, strings, keywords, byte strings |
| `RivestSExp` (canonical) | octet strings |
| `HintedSExp` (display hints) | an octet string with an optional hint |

Mixed families use `Atom ks`: an atom of one of the kinds `ks : List AtomKind`, so a symbol
and a string with the same text are different atoms (`Atom.kind`).

**Rivest S-expressions.** The data model of RFC 9804 (`Silmaril.Formats.Spki.Sexp`) has
octet-string atoms with an optional *display hint*; the canonical encoding writes the hint
(`[hint]octets`), so hints are part of the data. `RivestSExp = SExp Bytes`
(`Silmaril.Formats.RivestSExp`) is the hint-free model of the older canonical reader;
`HintedSExp` carries hints, `toSpki` maps it onto `Spki.Sexp`, and `RivestSExp`-style trees
embed with no hint (`Thms`).

## Tagged ASTs with typed payloads

A signature `AstSig` has tags, a payload type `Arg t` per tag and an arity per tag (`Arity`: a
natural number, or `star` for any number of children). Its trees are
`AST S := TExpr1 (Σ t, S.Arg t)`: tagged expressions whose tag is a tag with its payload; the
arity is the predicate `WellArity`. `WitSig` gives payloads as vectors of WIT-like value types
(`PTy`: `bool`, `s32`, `u32`, `s64`, `u64`, `string`, `list<u8>`, `list<T>`), so the import
`tag(args…, children…)` of a tag has typed, heterogeneous arguments (`PTy.Vals`).

The S-expression signature `sexpSig α` has **one** payload-free variadic branch tag and one
nullary leaf tag carrying an atom. Proper S-expressions are exactly its well-arity trees
(`SExp.equivAST`, `Thms`). The leaf is a *tag of arity 0*, not an unlabelled internal node: in
`TExpr1 α` (every node an atom label with children, `≃ Tree2 α`) an atom could have children,
and `sexpSig` without `WellArity` would allow a leaf with children too.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Formats

universe u v

/-! ## Atom kinds -/

/-- Atom kinds. -/
inductive AtomKind where
  | symbol
  | string
  | bytes
  | word
  | keyword
  deriving DecidableEq, Repr

/-- The payload of each atom kind; a word is an `i64`. -/
abbrev AtomKind.Val : AtomKind → Type
  | .symbol => String
  | .string => String
  | .bytes => List UInt8
  | .word => BitVec 64
  | .keyword => String

/-- An atom of one of the kinds `ks`. -/
structure Atom (ks : List AtomKind) where
  kind : AtomKind
  mem : kind ∈ ks
  val : kind.Val

abbrev SymbolSExp := SExp String
abbrev ByteSExp := SExp (List UInt8)
abbrev WordSExp := SExp (BitVec 64)
abbrev SymStrSExp := SExp (Atom [.symbol, .string])
abbrev SymBytesSExp := SExp (Atom [.symbol, .bytes])
abbrev SymStrBytesSExp := SExp (Atom [.symbol, .string, .bytes])
abbrev SymStrKwSExp := SExp (Atom [.symbol, .string, .keyword])
abbrev SymStrKwBytesSExp := SExp (Atom [.symbol, .string, .keyword, .bytes])

/-- A display-hinted octet string: the RFC 9804 atom. -/
abbrev Hinted := Option (List UInt8) × List UInt8

/-- Rivest S-expressions with display hints. -/
abbrev HintedSExp := SExp Hinted

/-! ## Payload types -/

/-- WIT-like payload value types. -/
inductive PTy where
  | bool
  | s32
  | u32
  | s64
  | u64
  | string
  | bytes
  | list (t : PTy)
  deriving DecidableEq, Repr

/-- The values of a payload type. -/
def PTy.Val : PTy → Type
  | .bool => Bool
  | .s32 => Int32
  | .u32 => UInt32
  | .s64 => Int64
  | .u64 => UInt64
  | .string => String
  | .bytes => List UInt8
  | .list t => List t.Val

/-- The values of a vector of payload types. -/
def PTy.Vals : List PTy → Type
  | [] => Unit
  | t :: ts => t.Val × PTy.Vals ts

/-! ## Signatures -/

/-- The number of children a tag takes. -/
inductive Arity where
  | fixed (n : Nat)
  | star
  deriving DecidableEq, Repr

/-- `n` children are admitted. -/
def Arity.Admits : Arity → Nat → Bool
  | .fixed m, n => n == m
  | .star, _ => true

/-- **An AST signature**: tags, payloads and arities. -/
structure AstSig where
  Tag : Type
  Arg : Tag → Type
  arity : Tag → Arity

/-- A signature with WIT-typed payload vectors. -/
structure WitSig where
  Tag : Type
  params : Tag → List PTy
  arity : Tag → Arity

def WitSig.toAstSig (S : WitSig) : AstSig := ⟨S.Tag, fun t => PTy.Vals (S.params t), S.arity⟩

/-- **The trees of a signature**: tagged expressions whose tag carries its payload. -/
abbrev AST (S : AstSig) := TExpr1 (Σ t, S.Arg t)

namespace AST

variable {S : AstSig}

/-- A node from a list of children. -/
def node (t : S.Tag) (a : S.Arg t) (children : List (AST S)) : AST S :=
  TExpr.ofList ⟨t, a⟩ children

/-- **Every node has an admitted number of children.** -/
def WellArity : AST S → Prop
  | .atom e => e.elim
  | .tag ⟨t, _⟩ n children => (S.arity t).Admits n = true ∧ ∀ i, WellArity (children i)

end AST

/-! ## The S-expression signature -/

/-- The two tags of S-expressions. -/
inductive SxTag where
  | branch
  | leaf
  deriving DecidableEq, Repr

/-- **The S-expression signature**: a payload-free variadic branch and a nullary leaf with an
atom. -/
def sexpSig (α : Type) : AstSig where
  Tag := SxTag
  Arg
    | .branch => Unit
    | .leaf => α
  arity
    | .branch => .star
    | .leaf => .fixed 0

namespace SExp

variable {α : Type}

/-- S-expressions as `sexpSig` trees. -/
def toAST : SExp α → AST (sexpSig α)
  | .atom a => .tag ⟨SxTag.leaf, a⟩ 0 Fin.elim0
  | .list n children => .tag ⟨SxTag.branch, ()⟩ n fun i => toAST (children i)

end SExp

namespace AST

variable {α : Type}

/-- `sexpSig` trees as S-expressions (a leaf's children, if any, are dropped). -/
def toSExp : AST (sexpSig α) → SExp α
  | .atom e => e.elim
  | .tag ⟨SxTag.leaf, a⟩ _ _ => .atom a
  | .tag ⟨SxTag.branch, _⟩ n children => .list n fun i => toSExp (children i)

end AST

/-- **The proper part of a dotted S-expression**: its n-ary form when it is proper (the unique
preimage under `SExp.toSExp2`, by classical choice), `none` for improper ones. -/
noncomputable def SExp2.toSExp? {α : Type} (x : SExp2 α) : Option (SExp α) :=
  open Classical in if h : ∃ e : SExp α, e.toSExp2 = x then some h.choose else none

/-- Hinted S-expressions as RFC 9804 S-expressions. -/
def HintedSExp.toSpki : HintedSExp → Spki.Sexp
  | .atom (hint, octets) => .atom hint octets
  | .list _ children => .list (List.ofFn fun i => toSpki (children i))

end Silmaril.Formats
