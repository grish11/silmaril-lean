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
arity is the predicate `WellArity`. `WitSig` gives payloads as vectors of WIT value types
(`PTy`: `bool`, the eight integer types, `f32`, `f64`, `char`, `string`, `list<T>` (so
`list<u8>`), `list<T, N>`, records, tuples, variants, enums, options, results, flags and the
handles `own<R>` (a resource representation) and `borrow<R>` (no value in a stored tree)), so
the import `tag(args…, children…)` of a tag has typed, heterogeneous arguments (`PTy.Vals`).

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

/-- **WIT payload value types**: the WIT value types with a canonical-ABI memory representation
and no asynchronous semantics, and the resource handles `own<r>`, `borrow<r>` of resource type
number `r` (`Silmaril.Wasm.Game.HandleAccept.Wit.toWit` maps them injectively onto
`WIT.ValType _ Nat`). Field, case and label names are kept, as in WIT; `bytes` is `list<u8>`
(`PTy.bytes`). Not payload types: `future`, `stream`, `error-context` (asynchronous endpoints,
unsupported pending async semantics) and `map` (a despecialised list of pairs: use
`list (tuple [k, v])`).

**Handles in stored trees.** A tree outlives the call that built it, so its payload values
cannot be handle indices of the module's table:

* `own r`: the value is the resource's **representation** (`Nat`, as `Value.Val.own` carries
  it), read from an explicit resource table at the call that moves the handle into the tree
  (`Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own`): the owned handle is consumed once;
* `borrow r`: **no value** (`Empty`). A borrow lives only for one call, so a tree cannot store
  one: a payload with a `borrow` field has no value and decodes to no event. -/
inductive PTy where
  | bool
  | s32
  | u32
  | s64
  | u64
  | string
  | list (t : PTy)
  | s8
  | u8
  | s16
  | u16
  | f32
  | f64
  | char
  | fixedList (t : PTy) (n : Nat)
  | record (fields : List (String × PTy))
  | tuple (ts : List PTy)
  | variant (cases : List (String × Option PTy))
  | enum (cases : List String)
  | option (t : PTy)
  | result (ok err : Option PTy)
  | flags (labels : List String)
  | own (r : Nat)
  | borrow (r : Nat)
  deriving Repr

/-- `list<u8>`: byte strings. -/
abbrev PTy.bytes : PTy := .list .u8

mutual
/-- **The values of a payload type** (the Lean interpretation `WIT.ValType.Interp` of its WIT
type): integers as Lean's fixed-width integers, floats as their IEEE 754 bit patterns
(`BitVec 32`, `BitVec 64`; the canonical ABI canonicalises NaNs on lift), `char` as a Unicode
scalar value (`Char`), records and tuples as right-nested products ending in `Unit` (names
dropped), variants as right-nested sums ending in `Empty` (a case without payload carries
`Unit`), `enum` with `n` cases as `Fin n`, `flags` with `n` labels as `BitVec n` (bit `i` is
label `i`), `result` as `ok ⊕ err`, `own r` as the resource's representation `Nat` (never
the handle index), `borrow r` as `Empty` (no stored tree holds a borrow). -/
def PTy.Val : PTy → Type
  | .bool => Bool
  | .s32 => Int32
  | .u32 => UInt32
  | .s64 => Int64
  | .u64 => UInt64
  | .string => String
  | .list t => List t.Val
  | .s8 => Int8
  | .u8 => UInt8
  | .s16 => Int16
  | .u16 => UInt16
  | .f32 => BitVec 32
  | .f64 => BitVec 64
  | .char => Char
  | .fixedList t n => Vector t.Val n
  | .record fs => PTy.FieldVals fs
  | .tuple ts => PTy.Vals ts
  | .variant cs => PTy.CaseVals cs
  | .enum cs => Fin cs.length
  | .option t => Option t.Val
  | .result ok err => PTy.OptVal ok ⊕ PTy.OptVal err
  | .flags ls => BitVec ls.length
  | .own _ => Nat
  | .borrow _ => Empty

/-- The values of a vector of payload types: a right-nested product. -/
def PTy.Vals : List PTy → Type
  | [] => Unit
  | t :: ts => t.Val × PTy.Vals ts

/-- The values of record fields: a right-nested product. -/
def PTy.FieldVals : List (String × PTy) → Type
  | [] => Unit
  | (_, t) :: fs => t.Val × PTy.FieldVals fs

/-- The values of variant cases: a right-nested sum. -/
def PTy.CaseVals : List (String × Option PTy) → Type
  | [] => Empty
  | (_, o) :: cs => PTy.OptVal o ⊕ PTy.CaseVals cs

/-- An optional payload: `Unit` when absent. -/
def PTy.OptVal : Option PTy → Type
  | none => Unit
  | some t => t.Val
end

mutual
/-- Boolean equality of payload types (`DecidableEq PTy` in `Thms`: the derived handler does
not cover the nesting through `List (String × _)`). -/
def PTy.beq : PTy → PTy → Bool
  | .bool, .bool | .s32, .s32 | .u32, .u32 | .s64, .s64 | .u64, .u64 | .string, .string
  | .s8, .s8 | .u8, .u8 | .s16, .s16 | .u16, .u16 | .f32, .f32 | .f64, .f64
  | .char, .char => true
  | .list a, .list b => PTy.beq a b
  | .fixedList a n, .fixedList b m => PTy.beq a b && n == m
  | .record fs, .record gs => PTy.beqFields fs gs
  | .tuple ts, .tuple us => PTy.beqList ts us
  | .variant cs, .variant ds => PTy.beqCases cs ds
  | .enum cs, .enum ds => cs == ds
  | .option a, .option b => PTy.beq a b
  | .result a b, .result c d => PTy.beqOpt a c && PTy.beqOpt b d
  | .flags ls, .flags ms => ls == ms
  | .own r, .own q | .borrow r, .borrow q => r == q
  | _, _ => false
  termination_by structural a _ => a

/-- `PTy.beq` on lists. -/
def PTy.beqList : List PTy → List PTy → Bool
  | [], [] => true
  | a :: as, b :: bs => PTy.beq a b && PTy.beqList as bs
  | _, _ => false
  termination_by structural as _ => as

/-- `PTy.beq` on record fields (names included). -/
def PTy.beqFields : List (String × PTy) → List (String × PTy) → Bool
  | [], [] => true
  | (n, a) :: as, (m, b) :: bs => n == m && PTy.beq a b && PTy.beqFields as bs
  | _, _ => false
  termination_by structural as _ => as

/-- `PTy.beq` on variant cases (names included). -/
def PTy.beqCases : List (String × Option PTy) → List (String × Option PTy) → Bool
  | [], [] => true
  | (n, a) :: as, (m, b) :: bs => n == m && PTy.beqOpt a b && PTy.beqCases as bs
  | _, _ => false
  termination_by structural as _ => as

/-- `PTy.beq` on optional types. -/
def PTy.beqOpt : Option PTy → Option PTy → Bool
  | none, none => true
  | some a, some b => PTy.beq a b
  | _, _ => false
  termination_by structural a _ => a
end

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
