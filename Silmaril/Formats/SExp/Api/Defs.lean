module

public import Silmaril.Formats.SExp.Family.Defs
public import Silmaril.Semantics.Accept.Handle.Defs

/-!
# Handle APIs for S-expressions, dotted S-expressions and tagged ASTs

Instances of the writer and reader signatures of `Silmaril.Semantics.Accept.Handle` for the tree
families of `Silmaril.Formats.SExp.Family`. Each writer operation is one import of the API; the
Wasm layer (`Silmaril.Wasm.Game.HandleAccept`) decodes calls into these operations.

## Writers

* `sexpW α` (n-ary): `atom a` (`symbol(string)`, `string(string)`, `blob(list<u8>)`,
  `word(i64)`, `keyword(string)` for the family's atom kinds) and `list`
  (`sexp(list<i32>) -> i32`, any number of children).
* `astW S` (tagged ASTs): one operation per tag *with its payload*, `tag(args…, children…)`;
  the arity (`AstSig.arity`) decides how many children are admitted. Variadic imports
  `tag(args…, children: list<i32>)` and fixed-arity imports `tag(args…, c₁, …, cₙ)` are two
  decodings of the same operation; a mixed signature uses either per tag.
* `consW α` (dotted, `SExp2`): `nil()`, `atom a`, `cons(i32, i32)`. Improper lists are
  constructible.
* `pairW α` (cons without a distinguished `nil`, `Tree2`): `atom a`, `cons(i32, i32)`.

`SxOp.toAST` maps the S-expression writer into the AST writer of `sexpSig α`; it is a writer
homomorphism along `SExp.toAST` (`Thms`), so every first-class S-expression API is the generic
AST API at that signature.

## Readers

* `sexpR α H`: `kind(h)` (atom or list), `atom(h) -> α` (`symbol(i32) -> string` etc.),
  `items(h) -> list<i32>` (the `sexp(i32) -> list<i32>` query), `count(h)` and `child(h, i)`
  (the `children(i32) -> i32` / `child(i32, i32) -> i32` alternative). Child handles are any
  handles denoting the children (a relation, not a function).
* `consR α H`: `kind(h)` (nil, atom or cons), `atom(h)`, `car(h)`, `cdr(h)`.
* `astR S H`: `tag(h)` (tag and payload), `count(h)`, `child(h, i)`.

Every reader is monotone (`Thms`), so in combined sessions every answer stays correct.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Formats.Api

open Silmaril.Accept.Handle

universe u

variable {α : Type} {H : Type}

/-! ## Writers -/

/-- Operations of the n-ary S-expression writer. -/
inductive SxOp (α : Type) where
  | atom (a : α)
  | list

/-- **The n-ary S-expression writer**. -/
def sexpW (α : Type) : Writer (SxOp α) (SExp α) where
  build
    | .atom a, [] => some (.atom a)
    | .list, cs => some (SExp.ofList cs)
    | _, _ => none

/-- An S-expression operation as an `sexpSig` tag with payload. -/
def SxOp.toAST : SxOp α → Σ t, (sexpSig α).Arg t
  | .atom a => ⟨SxTag.leaf, a⟩
  | .list => ⟨SxTag.branch, ()⟩

/-- **The generic tagged-AST writer**: a tag with its payload, and children admitted by its
arity. -/
def astW (S : AstSig) : Writer (Σ t, S.Arg t) (AST S) where
  build op cs := if (S.arity op.1).Admits cs.length then some (TExpr.ofList op cs) else none

/-- Operations of the dotted (cons) writer. -/
inductive ConsOp (α : Type) where
  | nil
  | atom (a : α)
  | cons

/-- **The cons writer** for dotted S-expressions. -/
def consW (α : Type) : Writer (ConsOp α) (SExp2 α) where
  build
    | .nil, [] => some .nil
    | .atom a, [] => some (.atom a)
    | .cons, [x, y] => some (.cons x y)
    | _, _ => none

/-- Operations of the binary-tree writer (no distinguished `nil`). -/
inductive PairOp (α : Type) where
  | atom (a : α)
  | cons

/-- **The cons writer without `nil`**, for binary trees. -/
def pairW (α : Type) : Writer (PairOp α) (Tree2 α) where
  build
    | .atom a, [] => some (.atom a)
    | .cons, [x, y] => some (.cons x y)
    | _, _ => none

/-- `c` is a child of the list `e`. -/
def SExp.Child (c e : SExp α) : Prop := ∃ cs, e = SExp.ofList cs ∧ c ∈ cs

/-- `c` is the car or the cdr of `e`. -/
def SExp2.Child (c e : SExp2 α) : Prop := ∃ x y, e = .cons x y ∧ (c = x ∨ c = y)

/-! ## Readers -/

/-- S-expression queries. -/
inductive SxQ (H : Type) where
  | kind (h : H)
  | atom (h : H)
  | items (h : H)
  | count (h : H)
  | child (h : H) (i : Nat)

/-- S-expression answers. -/
inductive SxA (α : Type) (H : Type) where
  | isList (b : Bool)
  | atom (a : α)
  | items (hs : List H)
  | count (n : Nat)
  | handle (h : H)

/-- Whether an S-expression is a list. -/
def isList : SExp α → Bool
  | .atom _ => false
  | .list _ _ => true

/-- **The S-expression reader.** -/
def sexpR (α : Type) (H : Type) : Reader (SxQ H) (SxA α H) H (SExp α) where
  valid ρ
    | .kind h => ∃ x, ρ h = some x
    | .atom h => ∃ a, ρ h = some (.atom a)
    | .items h => ∃ cs, ρ h = some (SExp.ofList cs)
    | .count h => ∃ cs, ρ h = some (SExp.ofList cs)
    | .child h i => ∃ cs, ρ h = some (SExp.ofList cs) ∧ i < cs.length
  ok ρ q a := match q, a with
    | .kind h, .isList b => ∃ x, ρ h = some x ∧ b = isList x
    | .atom h, .atom a => ρ h = some (.atom a)
    | .items h, .items hs =>
        ∃ cs, ρ h = some (SExp.ofList cs) ∧ List.Forall₂ (fun h c => ρ h = some c) hs cs
    | .count h, .count n => ∃ cs, ρ h = some (SExp.ofList cs) ∧ cs.length = n
    | .child h i, .handle h' => ∃ cs c, ρ h = some (SExp.ofList cs) ∧ cs[i]? = some c ∧
        ρ h' = some c
    | _, _ => False

/-- Dotted S-expression queries. -/
inductive ConsQ (H : Type) where
  | kind (h : H)
  | atom (h : H)
  | car (h : H)
  | cdr (h : H)

/-- The three kinds of dotted S-expression nodes. -/
inductive ConsKind where
  | nil
  | atom
  | cons
  deriving DecidableEq

/-- Dotted S-expression answers. -/
inductive ConsA (α : Type) (H : Type) where
  | kind (k : ConsKind)
  | atom (a : α)
  | handle (h : H)

/-- The kind of a dotted S-expression. -/
def consKind : SExp2 α → ConsKind
  | .nil => .nil
  | .atom _ => .atom
  | .cons _ _ => .cons

/-- **The dotted S-expression reader.** -/
def consR (α : Type) (H : Type) : Reader (ConsQ H) (ConsA α H) H (SExp2 α) where
  valid ρ
    | .kind h => ∃ x, ρ h = some x
    | .atom h => ∃ a, ρ h = some (.atom a)
    | .car h => ∃ x y, ρ h = some (.cons x y)
    | .cdr h => ∃ x y, ρ h = some (.cons x y)
  ok ρ q a := match q, a with
    | .kind h, .kind k => ∃ x, ρ h = some x ∧ k = consKind x
    | .atom h, .atom a => ρ h = some (.atom a)
    | .car h, .handle h' => ∃ x y, ρ h = some (.cons x y) ∧ ρ h' = some x
    | .cdr h, .handle h' => ∃ x y, ρ h = some (.cons x y) ∧ ρ h' = some y
    | _, _ => False

/-- AST queries. -/
inductive AstQ (H : Type) where
  | tag (h : H)
  | count (h : H)
  | child (h : H) (i : Nat)

/-- AST answers. -/
inductive AstA (S : AstSig) (H : Type) where
  | tag (v : Σ t, S.Arg t)
  | count (n : Nat)
  | handle (h : H)

/-- **The AST reader.** -/
def astR (S : AstSig) (H : Type) : Reader (AstQ H) (AstA S H) H (AST S) where
  valid ρ
    | .tag h => ∃ x, ρ h = some x
    | .count h => ∃ x, ρ h = some x
    | .child h i => ∃ v cs, ρ h = some (TExpr.ofList v cs) ∧ i < cs.length
  ok ρ q a := match q, a with
    | .tag h, .tag v => ∃ cs, ρ h = some (TExpr.ofList v cs)
    | .count h, .count n => ∃ v cs, ρ h = some (TExpr.ofList v cs) ∧ cs.length = n
    | .child h i, .handle h' => ∃ v cs c, ρ h = some (TExpr.ofList v cs) ∧ cs[i]? = some c ∧
        ρ h' = some c
    | _, _ => False

/-! ## Certificates for dotted lists of atoms -/

/-- **A read history certifies** that `h` is the proper dotted list of the atoms `as`: a chain
of `kind`, `car`, `cdr` and `atom` answers ending in `nil`. -/
inductive ConsChain {α : Type} {H : Type} (hist : List (ConsQ H × ConsA α H)) :
    H → List α → Prop where
  | nil {h : H} : (.kind h, .kind .nil) ∈ hist → ConsChain hist h []
  | cons {h hcar hcdr : H} {a : α} {as : List α} :
      (.kind h, .kind .cons) ∈ hist → (.car h, .handle hcar) ∈ hist →
      (.cdr h, .handle hcdr) ∈ hist → (.atom hcar, .atom a) ∈ hist →
      ConsChain hist hcdr as → ConsChain hist h (a :: as)

/-- The certificate of "a proper list of atoms satisfying `P`". -/
def listCert {α : Type} {H : Type} (P : List α → Prop) (hist : List (ConsQ H × ConsA α H))
    (h : H) : Prop :=
  ∃ as, ConsChain hist h as ∧ P as

end Silmaril.Formats.Api
