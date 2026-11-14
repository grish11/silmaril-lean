module

public import Silmaril.Wasm.Cfg.BlockCfg.Defs

@[expose] public section

/-!
# CFG variants: traps as an abrupt outcome instead of a sink node

The legacy block CFG (`Cfg.Edge`, `Silmaril.Wasm.Cfg.BlockCfg`) draws a trap as an edge to the
sink node `trap`. Variant **TE** ("trap as effect") keeps everything else and removes that sink:

* `EdgeTE body b t`: the legacy edges whose target is not `trap`;
* `mustTrap body b`: block `b` ends in `unreachable`, so every run reaching its end stops with a
  trap. That is an *abrupt, non-returning outcome*, not an ordinary state effect, and such a
  block has no successors in TE.

The may-trap marks of ordinary instructions (`Cfg.Effect.mayTrap`) are unchanged and stay
distinct from `mustTrap`. Raises are not changed here: the handler-resolved raise edges are the
next step of this variant (`docs/projects/wasm-cfg.md`, "CFG variants").

`Thms`: the translation back, `edge_iff_te` — a legacy edge is a TE edge, or the `trap` edge of
a `mustTrap` block, and nothing else. So TE together with its marks determines the legacy graph,
and conversely.
-/

namespace Silmaril.Wasm.Cfg

/-- **TE edges**: the legacy edges that do not go to the `trap` sink. -/
def EdgeTE (body : Expr) (b : BlockId) (t : Target) : Prop := Edge body b t ∧ t ≠ .trap

/-- **Must-trap outcome**: the block's terminator is `unreachable`. -/
def mustTrap (body : Expr) (b : BlockId) : Prop :=
  ∃ s, lookup body b = some s ∧ s.term = some .unreachable

/-- The TE successors of a block: the legacy ones without `trap`. -/
def succTE (body : Expr) (b : BlockId) (s : Segment) : List Target :=
  (succOf body b s).filter (· != .trap)

end Silmaril.Wasm.Cfg
