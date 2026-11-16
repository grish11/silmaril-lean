module

public import Silmaril.Wasm.Examples.JsonAccept.Defs
public import Silmaril.Semantics.Acceptors.Defs

/-! # The JSON-subset acceptor, incrementally: definitions

The automaton of the verified Wasm module `prog` (`stepN`, the transition its loop body
computes) as an incremental acceptor of `Silmaril.Semantics.Acceptors`:

* `symbolAcceptor`: state the automaton state (a `Nat`, initially `0`); `process` is one step on
  a byte, `query` answers whether the state is accepting (`2 ≤ q ≤ 4`, the module's final test)
  and leaves the state unchanged, `reset` returns to `0`;
* `streamAcceptor χ`: the same on chunks of any `ChunkView χ UInt8` (byte lists, `Array UInt8`,
  `ByteArray`), byte by byte (`Acceptor.ofSymbols`).

This is a Lean function, not a second Wasm module: the Wasm module reads its whole input at once.
`Thms` proves this acceptor correct and relates its answers to the module's verdict.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.JsonAccept

/-- The accepting states of the automaton, as a test. -/
def accepting (q : Nat) : Bool := decide (2 ≤ q ∧ q ≤ 4)

/-- **The automaton of `prog`, one byte at a time.** -/
def symbolAcceptor : Silmaril.Acceptor Nat UInt8 where
  init := 0
  process q b := stepN q b.toNat
  query q := (accepting q, q)
  reset _ := 0

/-- **The automaton of `prog`, one chunk at a time.** -/
def streamAcceptor (χ : Type) [Silmaril.ChunkView χ UInt8] : Silmaril.Acceptor Nat χ :=
  symbolAcceptor.ofSymbols

end Silmaril.Wasm.Examples.JsonAccept
