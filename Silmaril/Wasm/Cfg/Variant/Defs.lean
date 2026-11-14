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

/-! ## Variant AE: traps and raises both as outcomes, with handlers

The all-effects block graph keeps the edges that are neither `trap` nor `raise` nor a
`try_table`'s catch edge. A block's abrupt endings are *outcomes*, not edges:
- `mustTrap`: the block ends in `unreachable`;
- `mustRaise`: the block ends in `throw`/`throw_ref`;
- may-trap and call marks (`blockEffects`) for its other instructions.

A raise is resolved to its possible handlers, `raiseHandlers body p`, for a raise in
sequence `p`. These are the catch targets of the enclosing `try_table`s, innermost first, each
resolved outside its `try_table` (as `Step/throw_ref-handler-catch*` branches there). The
search stops at a `try_table` with a `catch_all`/`catch_all_ref`; otherwise `raise` (the caller)
ends the list. Typed `catch` clauses match by tag at run time, so each listed handler is a
possible one. -/

/-- The AE successors of a block. A `try_table` block only enters its body: its catch targets
are reached by raises, as handler outcomes of the raising blocks, not by an edge from the
`try_table`. Otherwise these are the legacy successors without `trap` and `raise`. -/
def succAE (body : Expr) (b : BlockId) (s : Segment) : List Target :=
  match s.term with
  | some (.tryTable ..) => [entry body (b.seq ++ [(b.idx, 0)]) 0]
  | _ => (succOf body b s).filter fun t => t != .trap && t != .raise

/-- **AE edges.** -/
def EdgeAE (body : Expr) (b : BlockId) (t : Target) : Prop :=
  ∃ s, lookup body b = some s ∧ t ∈ succAE body b s

/-- A legacy catch edge: from a `try_table` block to one of its catch targets. -/
def catchEdge (body : Expr) (b : BlockId) (t : Target) : Prop :=
  ∃ s bt cs bd, lookup body b = some s ∧ s.term = some (.tryTable bt cs bd) ∧
    t ∈ cs.map fun c => resolveT (labels body b.seq) (catchLabel c)

/-- **Must-raise outcome**: the block's terminator is `throw` or `throw_ref`. -/
def mustRaise (body : Expr) (b : BlockId) : Prop :=
  ∃ s, lookup body b = some s ∧ ((∃ x, s.term = some (.throw x)) ∨ s.term = some .throwRef)

/-- Whether a catch clause catches every exception. -/
def Catch.catchesAll : Catch → Bool
  | .catchAll _ | .catchAllRef _ => true
  | _ => false

/-- The possible handlers of a raise in the sequence at the reversed path `rp`. -/
def handlersRev (body : Expr) : List SeqStep → List Target
  | [] => [.raise]
  | (m, _) :: rp =>
    match lookup body ⟨rp.reverse, m⟩ with
    | some ⟨_, some (.tryTable _ cs _)⟩ =>
      let here := cs.map fun c => resolveT (labels body rp.reverse) (catchLabel c)
      if cs.any Catch.catchesAll then here else here ++ handlersRev body rp
    | _ => handlersRev body rp

/-- **The possible handlers of a raise in sequence `p`**: catch targets, then `raise` (the
caller) unless a `catch_all` intervenes. -/
def raiseHandlers (body : Expr) (p : List SeqStep) : List Target := handlersRev body p.reverse

end Silmaril.Wasm.Cfg
