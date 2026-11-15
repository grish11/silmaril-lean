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

end Silmaril.Wasm.Cfg
