module

public import Silmaril.Wasm.Cfg.Variant.Defs

@[expose] public section

/-!
# Maximal basic blocks: the contracted graph

`Cfg.canMerge` (`Variant`) says when block `c` continues block `b` inside one maximal block: `b`'s
only all-effects (AE) successor is `c`, no other block has an AE or handler edge into `c`, and `c`
is not the entry. A maximal block is a chain of such merges (`Thms`: merges are functional and
injective, so chains are disjoint paths starting outside the merge targets).

The contracted graph keeps every AE edge of every member **except the merged fall-through edges
themselves** (`internal`), and every handler edge. Mapping each member to its maximal block gives
the edges the explorer publishes (`all-effects-max`). In particular a loop back to the chain's own
head, and a one-block loop, stay edges of the contracted graph; label targets, loop heads and
handler entries stay block boundaries (`canMerge_pred`).

This is a graph construction over the syntactic AE graph. It says nothing about executions.
-/

namespace Silmaril.Wasm.Cfg

/-- The edge `b → t` is a merged fall-through: it lies inside one maximal block. -/
def internal (body : Expr) (b : BlockId) : Target → Bool
  | .block c => canMerge body b c
  | _ => false

/-- The AE edges kept in the contracted graph, by member block: all but the merged fall-throughs. -/
def maxFlow (body : Expr) : List (BlockId × Target) :=
  (blocks body).flatMap fun p => ((succAE body p.1 p.2).filter fun t => !internal body p.1 t).map (p.1, ·)

/-- The handler edges of the contracted graph, by member block (all of them are kept). -/
def maxHandler (body : Expr) : List (BlockId × Target) :=
  (blocks body).flatMap fun p => (handlerSucc body p.1 p.2).map (p.1, ·)

/-- A handler edge: from a block that may raise to a possible handler. -/
def HandlerEdge (body : Expr) (b : BlockId) (t : Target) : Prop :=
  ∃ s, lookup body b = some s ∧ t ∈ handlerSucc body b s

/-! ## The grouping into maximal blocks, and its checker

`maxGroups` builds the maximal blocks: from each block no merge reaches (`isHead`), follow the
unique merge (`mergeTarget`) as far as it goes. `groupsOk` checks a grouping: the groups list
every block exactly once (`nodupB`, both inclusions), consecutive members merge (`chainOk`), a
group starts at a block no merge reaches and ends at a block that merges into none. `Thms`
proves what `groupsOk` guarantees (`groupsOk_sound`, `groupOk_spec`); `wasm-pages` publishes a
maximal graph only for a grouping it accepts. -/

/-- The block `b` merges into, if any (its only AE successor, when `canMerge` holds). -/
def mergeTarget (body : Expr) (b : BlockId) : Option BlockId :=
  match lookup body b with
  | some s => match succAE body b s with
    | [.block c] => if canMerge body b c then some c else none
    | _ => none
  | none => none

/-- No block merges into `h`. -/
def isHead (body : Expr) (h : BlockId) : Bool := (blocks body).all fun p => !canMerge body p.1 h

/-- `l` merges into no block. -/
def isLast (body : Expr) (l : BlockId) : Bool := (blocks body).all fun p => !canMerge body l p.1

/-- The chain of merges from `b`, at most `n` steps long. -/
def chainFrom (body : Expr) : Nat → BlockId → List BlockId
  | 0, b => [b]
  | n + 1, b => b :: match mergeTarget body b with
    | some c => chainFrom body n c
    | none => []

/-- The maximal blocks: the merge chain from every block no merge reaches. -/
def maxGroups (body : Expr) : List (List BlockId) :=
  ((blocks body).filter fun p => isHead body p.1).map fun p => chainFrom body (blocks body).length p.1

/-- Consecutive members of `g` merge. -/
def chainOk (body : Expr) (g : List BlockId) : Bool := (g.zip g.tail).all fun p => canMerge body p.1 p.2

/-- A list without repetitions (checked). -/
def nodupB : List BlockId → Bool
  | [] => true
  | a :: l => !l.contains a && nodupB l

/-- One maximal block: a merge chain from a block no merge reaches to a block that merges into none. -/
def groupOk (body : Expr) (g : List BlockId) : Bool :=
  chainOk body g && (match g.head? with | some h => isHead body h | none => false) &&
    (match g.getLast? with | some l => isLast body l | none => false)

/-- **The grouping checker**: every block exactly once, each group a maximal merge chain. -/
def groupsOk (body : Expr) (gs : List (List BlockId)) : Bool :=
  let ids := (blocks body).map (·.1)
  nodupB gs.flatten && ids.all (gs.flatten.contains ·) && gs.flatten.all (ids.contains ·) &&
    gs.all (groupOk body)

end Silmaril.Wasm.Cfg
