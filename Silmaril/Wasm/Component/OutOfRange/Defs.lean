module

public import Silmaril.Wasm.Component.DWiring.Defs
public import Silmaril.Wasm.Component.Adapter.Defs

/-!
# Out-of-range chatter and trap propagation: definitions

`widenH n` answers a call of an out-of-range function with the trap answer
`none` at once, with no visible move (`Silmaril.Wasm.Component.DWiring`). A
strategy above it that keeps calling out-of-range functions after each `none`
therefore makes `DStrategy.atSizes n k σ` diverge, although `σ` itself never
diverges. That divergence is created by the wiring; it is **not** a Wasm trap
(a trap is a visible answer `none`, a divergence is the absence of any answer).
This module names the strategies that cause it and the strategies that cannot.

* `spinR j`, `spinS j`: the strategy that answers every question by calling
  function `j` with the question's payload, forever, whatever the answers
  (in particular after each `none`). It has no internal steps, so it never
  diverges on its own.
* `TrapPropagating σ`: after receiving the trap answer `none` to a call below,
  `σ` makes no further call in that round: its next move, if any, is at its
  upper interface (necessarily the answer to the current question).
  `TrapAborting σ` (for an upper interface with `Option Payload` answers too) is
  the stronger Wasm reading: the next move answers the current question with a
  trap. This is the game-level shape of Core Wasm's rule that a trapping
  callee traps its caller.
* `TrapSilent h`: every question that the handler `h` answers without a call
  is answered with a trap. `widenH n` and `maskH e` are trap-silent; `implsH`
  is not (a `.const (some v)` target answers silently with a value).

The lower interfaces are written `sigO O = ⟨O, fun _ => Option Payload⟩`, which
covers `sigU` (`O = Nat × Payload`) and `sigN n` (`O = Fin n × Payload`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

/-- A signature whose answers are payloads or the trap `none`, with operations
`O`. `sigU = sigO (Nat × Payload)` and `sigN n = sigO (Fin n × Payload)`. -/
abbrev sigO (O : Type) : Sig.{0} := ⟨O, fun _ => Option Payload⟩

/-- The reduction semantics of `spinS j`: each question `(i, a)` calls `(j, a)`
and, whatever the answer, calls it again; there is no internal step and no
final configuration. -/
def spinR (j : Nat) : Reduction sigU sigU where
  Conf _ := PUnit
  start _ := PUnit.unit
  step _ _ := False
  call {q} _ m _ := m = (j, q.2)
  done _ _ := False

/-- **The out-of-range spinner**: answers every question by calling function
`j` forever, re-calling after every answer (in particular after every trap
answer `none`). -/
def spinS (j : Nat) : DStrategy sigU sigU := DStrategy.ofReduction (spinR j)

/-- **Trap propagation (round-ending form).** After the trap answer `none` to a
call below, the strategy's next move is at its upper interface: it makes no
further call below in that round. -/
def TrapPropagating {O : Type} {G : Sig.{0}} (σ : DStrategy (sigO O) G) : Prop :=
  ∀ (s : List (Move (sigO O) G)) (m : O) (y : Move (sigO O) G),
    s ++ [.inl (.ans m none), y] ∈ σ.toStrategy → ∃ g, y = .inr g

/-- **Trap propagation (Wasm form).** After the trap answer `none` to a call
below, the strategy's next move answers the current question with a trap. -/
def TrapAborting {O P : Type} (σ : DStrategy (sigO O) (sigO P)) : Prop :=
  ∀ (s : List (Move (sigO O) (sigO P))) (m : O) (y : Move (sigO O) (sigO P)),
    s ++ [.inl (.ans m none), y] ∈ σ.toStrategy → ∃ q, y = .inr (.ans q none)

/-- A handler is **trap-silent** if it answers without a call only with a trap. -/
def TrapSilent {E : Sig.{0}} {O : Type} (h : Handler E (sigO O)) : Prop :=
  ∀ q r, h q = .pure r → r = none

end Silmaril.Wasm.Component
