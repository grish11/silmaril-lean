module

public import Silmaril.Formats.SExp.Family.Defs

/-!
# Abstract tree acceptors: patterns, combinators and AST encodings

An abstract acceptor of trees `X` is a language `Set X` (no wrapper): union and intersection
are Mathlib's set lattice, images and preimages are `Set.image`/`Set.preimage` (for instance
along `SExp.toSExp2`, `SExp.toAST` or an AST encoding `AST.encode`).

## Patterns with acceptors as an extra atom

* `Pat α := SExp (α ⊕ Set (SExp α))`: an S-expression whose atoms are atoms (`inl`) or
  acceptors (`inr L`, a hole matching any member of `L`). `Pat.lang p` is the set of
  S-expressions matching `p`. Different holes are matched independently.
* `Pat2 α := SExp2 (α ⊕ Set (SExp2 α))` for dotted S-expressions (`nil` matches `nil`).
* `PatAST S := TExpr (Σ t, S.Arg t) (Set (AST S))` for ASTs: the atoms of `TExpr` are the
  holes, so the tag-and-payload nodes match literally.

**Combinators.** `tuple [L₁, …, Lₙ]` is the list `(a₁ … aₙ)` with `aᵢ ∈ Lᵢ`,
`pair L₁ L₂ = tuple [L₁, L₂]`, and `star L` the lists of any length with every element in `L`.
Because a list decomposes uniquely, `tuple` preserves intersections componentwise
(`Thms`), unlike projections of relations.

## ASTs as S-expressions

`AST.encode tagEnc argEnc` writes a node `t(args; children)` as the list
`(tagEnc t arg₁ … argₖ child₁ … childₙ)` with `argEnc t a = [arg₁, …, argₖ]`. It is injective
when `tagEnc` is injective, each `argEnc t` is injective and **has a fixed length per tag**
(`ArgLenFixed`); without the last condition the boundary between arguments and children is
ambiguous (`Examples`). `AST.encodeWith` generalizes to any per-tag layout
`node : ∀ t, S.Arg t → List (SExp β) → SExp β`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Formats

variable {α β : Type}

/-- S-expression patterns: atoms or acceptor holes. -/
abbrev Pat (α : Type) := SExp (α ⊕ Set (SExp α))

/-- **The S-expressions matching a pattern.** -/
def Pat.lang : Pat α → Set (SExp α)
  | .atom (.inl a) => {.atom a}
  | .atom (.inr L) => L
  | .list n ps => {x | ∃ cs : Fin n → SExp α, x = .list n cs ∧ ∀ i, cs i ∈ Pat.lang (ps i)}

/-- The ground pattern of an S-expression. -/
def Pat.ground (e : SExp α) : Pat α := e.map .inl

/-- Lists `(a₁ … aₙ)` with `aᵢ ∈ Lᵢ`. -/
def tuple (Ls : List (Set (SExp α))) : Set (SExp α) :=
  {x | ∃ cs, x = SExp.ofList cs ∧ List.Forall₂ (· ∈ ·) cs Ls}

/-- Pairs `(a b)` with `a ∈ L₁`, `b ∈ L₂`. -/
def pair (L₁ L₂ : Set (SExp α)) : Set (SExp α) := tuple [L₁, L₂]

/-- Lists of any length with every element in `L`. -/
def star (L : Set (SExp α)) : Set (SExp α) := {x | ∃ cs, x = SExp.ofList cs ∧ ∀ c ∈ cs, c ∈ L}

/-- Dotted S-expression patterns. -/
abbrev Pat2 (α : Type) := SExp2 (α ⊕ Set (SExp2 α))

/-- **The dotted S-expressions matching a pattern.** -/
def Pat2.lang : Pat2 α → Set (SExp2 α)
  | .nil => {.nil}
  | .atom (.inl a) => {.atom a}
  | .atom (.inr L) => L
  | .cons p q => {x | ∃ a b, x = .cons a b ∧ a ∈ Pat2.lang p ∧ b ∈ Pat2.lang q}

/-- The ground dotted pattern of a dotted S-expression. -/
def Pat2.ground (e : SExp2 α) : Pat2 α := e.map .inl

/-- **A proper pattern as a dotted pattern**: lists become `nil`-terminated spines and every
hole `L` becomes the hole of its image `SExp.toSExp2 '' L`. -/
def Pat.toPat2 : Pat α → Pat2 α
  | .atom (.inl a) => .atom (.inl a)
  | .atom (.inr L) => .atom (.inr (SExp.toSExp2 '' L))
  | .list _ ps => SExp2.ofList (List.ofFn fun i => Pat.toPat2 (ps i))

/-- AST patterns: tag-and-payload nodes with acceptor holes. -/
abbrev PatAST (S : AstSig) := TExpr (Σ t, S.Arg t) (Set (AST S))

/-- **The ASTs matching a pattern.** -/
def PatAST.lang {S : AstSig} : PatAST S → Set (AST S)
  | .atom L => L
  | .tag v n ps => {x | ∃ cs : Fin n → AST S, x = .tag v n cs ∧ ∀ i, cs i ∈ PatAST.lang (ps i)}

/-- The ground AST pattern of an AST. -/
def PatAST.ground {S : AstSig} (e : AST S) : PatAST S := e.map Empty.elim

namespace AST

variable {S : AstSig}

/-- **An AST as an S-expression** with a per-tag layout of the node. -/
def encodeWith (node : ∀ t, S.Arg t → List (SExp β) → SExp β) : AST S → SExp β
  | .atom e => e.elim
  | .tag ⟨t, a⟩ _ cs => node t a (List.ofFn fun i => encodeWith node (cs i))

/-- **The standard layout** `(tag arg₁ … argₖ child₁ … childₙ)`. -/
def encode (tagEnc : S.Tag → SExp β) (argEnc : ∀ t, S.Arg t → List (SExp β)) : AST S → SExp β :=
  encodeWith fun t a cs => SExp.ofList (tagEnc t :: argEnc t a ++ cs)

/-- Each tag's argument encoding has a fixed length. -/
def ArgLenFixed (argEnc : ∀ t, S.Arg t → List (SExp β)) : Prop :=
  ∀ t (a a' : S.Arg t), (argEnc t a).length = (argEnc t a').length

end AST

end Silmaril.Formats
