module

public import Silmaril.Wasi.Component.Consequence.Checkers.Defs

/-! # A stateful specification checker

A specification strategy for protocol 2: exports `axiom(v)`, `check(stmt) -> bool` and
`reset()`. A generating play is a sequence of operations (`Op`), each one call answered at once:
`axiom(enc a)` returns `[]` and adds `a`, `reset()` returns `[]` and empties the assumptions,
`check(enc c)` returns whether `c` is one of the assumptions of the current epoch. Read through
`exportStateful .call statefulFns Policy.list decA decC`, it accepts exactly the membership
rule on the current epoch's list (`Silmaril.Wasi.Component.Consequence.Stateful.Thms`).

It is a strategy defined in Lean (`Strategy.generate`), not a compiled component. The
specification answers immediately and from the state of the generating play only: plays in which
the caller interleaves extra calls not of this shape are pending (unanswered), never answered
differently.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence

open Silmaril.Games
open Silmaril.Wasm.Component (Val)

/-- The `axiom` function. -/
def axiomFn : FnName := ⟨"", "axiom"⟩

/-- The `reset` function. -/
def resetFn : FnName := ⟨"", "reset"⟩

/-- The exports of the stateful checker. -/
abbrev statefulExports : Set FnName := {axiomFn, checkFn, resetFn}

/-- The functions of the stateful protocol. -/
def statefulFns : StatefulFns := { add := axiomFn, claim := checkFn, reset := some resetFn }

/-- One operation of the caller. -/
inductive Op (C : Type) where
  | axiom (a : C)
  | reset
  | check (c : C)

variable {C : Type} [DecidableEq C]

/-- The two moves of an operation in the state `xs`. -/
def opMoves (enc : C → Val) (xs : List C) : Op C → List (Move (nsig ∅) (nsig statefulExports))
  | .axiom a => [.inr (.ask (⟨axiomFn, by simp⟩, [enc a])),
      .inr (.ans (⟨axiomFn, by simp⟩, [enc a]) (some []))]
  | .reset => [.inr (.ask (⟨resetFn, by simp⟩, [])),
      .inr (.ans (⟨resetFn, by simp⟩, []) (some []))]
  | .check c => [.inr (.ask (⟨checkFn, by simp⟩, [enc c])),
      .inr (.ans (⟨checkFn, by simp⟩, [enc c]) (some [.bool (decide (c ∈ xs))]))]

/-- The state after an operation. -/
def opNext (xs : List C) : Op C → List C
  | .axiom a => xs ++ [a]
  | .reset => []
  | .check _ => xs

/-- The play of a sequence of operations from the state `xs`. -/
def playOf (enc : C → Val) :
    List C → List (Op C) → List (Move (nsig ∅) (nsig statefulExports))
  | _, [] => []
  | xs, o :: os => opMoves enc xs o ++ playOf enc (opNext xs o) os

/-- **The stateful membership checker.** -/
def statefulMember (enc : C → Val) : Strategy (nsig ∅) (nsig statefulExports) :=
  Strategy.generate {s | ∃ os, s = playOf enc [] os}

/-- The stateful membership checker at `u32` assumptions and statements. -/
def statefulMemberU32 : Strategy (nsig ∅) (nsig statefulExports) :=
  statefulMember (C := BitVec 32) .u32

/-- One `u32` argument. -/
def u32Arg : List Val → Option (BitVec 32) := Accept.args1 Accept.ofU32?

end Silmaril.Wasi.Consequence
