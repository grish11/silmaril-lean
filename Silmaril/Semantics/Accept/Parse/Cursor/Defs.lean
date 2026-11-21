module

public import Silmaril.Semantics.Accept.Parse.Defs

/-!
# Parsing sessions: the effective cursor of chunked input

`Silmaril.Accept.Parse.consumed` counts the `used` of **every** `done() -> (used, tree)`
(`PEv.finish used h`) of a trace. Under the call-local overrun policies (`callTrap`, the default,
and `ignore`) an overrun (`used` larger than the buffered input) is answered without moving the
cursor, so `consumed` overcounts and the cursor laws of `Silmaril.Accept.Parse` are stated for
`sessionTrap` only.

`effConsumed n t` is the **effective consumed count** of the trace `t` from a buffer of `n`
values: it tracks the buffered length along the trace (a chunk `feed c` adds `c.length`) and
counts a `finish used h` only when `used` is within the buffered input at that point (an answered
finish, which advances the cursor); an overrun counts `0`. It is computed from the trace alone.
Other events (`parse`, `append`, `done`, `reset`) leave the count and the tracked length; the
laws are stated for chunk-only traces (`Silmaril.Accept.Parse.ChunkOnly`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Accept.Parse

universe u v

variable {V : Type u} {H : Type v}

/-- **The effective consumed count** of a trace from a buffer of `n` values: the `used` of the
finishes within the buffered input, the buffered length tracked along the chunks. -/
def effConsumed : Nat → List (PEv V H) → Nat
  | _, [] => 0
  | n, .feed c :: es => effConsumed (n + c.length) es
  | n, .finish k _ :: es => if k ≤ n then k + effConsumed (n - k) es else effConsumed n es
  | n, _ :: es => effConsumed n es

end Silmaril.Accept.Parse
