module

public import Silmaril.Wasm.Examples.JsonAccept.Exact.Thms
public import Silmaril.Semantics.Accept.Automata.Thms

/-! # The JSON-subset acceptor as a presented automaton

The automaton the verified Wasm module runs (`stepN`, from the packed transition rows) is a
Mathlib `DFA` over bytes, `intDFA`. It **presents** the subset, in the sense of
`Silmaril.Semantics.Accept.Automata` (#274): `DFAPresents intDFA intText`, so the module's exact
acceptance reads as acceptance of a finite automaton's language:

`exportAccepted P Hosts prog "accept" = {w | w ∈ intDFA.accepts ∧ w.length < 2 ^ 32}`.

The language is regular, so no grammar presentation (#277) is needed for it.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.JsonAccept

open Silmaril.Wasm.Game.Accept
open Silmaril.Wasm.Numerics (Profile)

/-- The module's automaton as a Mathlib DFA over bytes. -/
def intDFA : DFA UInt8 Nat where
  step q b := stepN q b.toNat
  start := 0
  accept := {q | 2 ≤ q ∧ q ≤ 4}

theorem intDFA_eval (w : List UInt8) : intDFA.eval w = runN 0 (w.map UInt8.toNat) := by
  simp [DFA.eval, DFA.evalFrom, runN, intDFA, List.foldl_map]

/-- **The DFA accepts exactly the integer texts.** -/
theorem intDFA_accepts : intDFA.accepts = intText := by
  ext w
  rw [DFA.mem_accepts, intDFA_eval, ← acc_iff]
  rfl

/-- The DFA presents the subset (`Silmaril.Accept.Automata.DFAPresents`). -/
theorem intDFA_presents : Silmaril.Accept.Automata.DFAPresents intDFA intText := intDFA_accepts

/-- **The embedded Wasm module accepts the DFA's language**, up to the ABI bound. -/
theorem exportAccepted_eq_dfa {P : Profile} {Hosts : Set (Silmaril.Wasm.Execution.Core.HostSemantics Nat)}
    {host : Silmaril.Wasm.Execution.Core.HostSemantics Nat} (hh : host ∈ Hosts) :
    exportAccepted P Hosts prog "accept" = {w | w ∈ intDFA.accepts ∧ w.length < 2 ^ 32} := by
  rw [exportAccepted_eq hh, intDFA_accepts]

end Silmaril.Wasm.Examples.JsonAccept
