module

public import Silmaril.Wasm.Component.Reference.Sound.Defs

/-!
# Adequacy of the component IR against the reference machine: definitions

For simple components (`Simple`, `Silmaril.Wasm.Component.Reference.Bridge`) this module
defines the two sides of the finite adequacy theorem (`Adequacy.Thms`):

* the **public component interaction equivalence** `RefPubEquiv P prof c c'`, defined on the
  reference machine only (no IR, no strategy): the same export types, and for every typed
  sequence of resolved export calls followed by a typed last call, the same terminating
  behaviours (`seqObs`: the results of the resolved calls and a returned or trapping last call,
  `Outcome.Term`), the machine running at the silmaril profile `P` and the component choice
  profile `prof`;
* the **trap-last plays** of the IR denotation `trapLastPlays σ`: the plays of `σ`, read at the
  untyped export interface `sigU` (`pubPlays`, so that components with different export
  counts can be compared), in which no answer follows a trap answer (`TrapLast`).

Why trap-last: the strategy of a core instance (`Silmaril.Wasm.Game.ScalarInstance.strategy`)
keeps its store after a trap and accepts further questions, while the reference machine
follows REF (`definitions.py`): a trap locks the whole store down (`Machine.trapCfg`,
`lockdown := true`), and every later host event, in particular a fresh `Store.invoke`, is
disabled (`HostReadyCfg`; REF asserts `not lockdown` in `Store.invoke`). After a trap there is
no further public interaction at this interface, so the reference cannot observe the IR's plays
after a trap answer. `trapLastPlays` is the projection of the IR to that interface. The full
strategy equality does not follow from `RefPubEquiv`: `Adequacy.Thms` gives a counterexample.

Scope and non-claims:

* `Simple` components, float-free (`Simple.FloatFree`), within the flat arities
  (`Simple.Arity`), whose module is instantiated as the IR assumes (`Simple.Inst`), with no
  imports. Every Core profile `P` and component choice profile `prof`; no determinism is
  assumed.
* Terminating outcomes only. The plays are finite: a diverging call and a call that never
  answers look the same, so `seqObs` drops divergence (and deadlock and cancellation, which
  never occur here), and nothing is claimed about them. The infinite and divergence case needs
  the game-level infinite closure (the `DStrategy` `div`/`inf` components) and is a separate,
  later obligation.
* This is not contextual full abstraction: the observer is the host calling exports in
  sequence, not an arbitrary component context.
* The parser from bytes to `Comp` (and to `Simple`) is not involved; its correctness is a
  separate, unclaimed obligation.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## The reference side -/

/-- A terminating outcome: returned results or a trap. -/
def Outcome.Term : Outcome → Prop
  | .returns (some _) => True
  | .traps => True
  | _ => False

/-- **The terminating public observations** of calling the exports `calls` of `c` in order
(each resolving) and then export `j` on `vs`, after instantiating `c.toRef` from the empty
store: the results of the resolved calls and the terminating outcome of the last call. -/
def seqObs (P : Profile) (prof : ProfileKind) (c : Simple)
    (calls : List (Fin c.exports.length × List IVal)) (j : Fin c.exports.length)
    (vs : List IVal) : Set (List (List Silmaril.Wasm.Component.Value.Val) × Outcome) :=
  {p | p ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal) ∧ p.2.Term}

/-- Calls of the exports of `c`, as calls of the exports of `c'` with the same indices. -/
def castCalls {c c' : Simple} (h : c.exports.length = c'.exports.length)
    (calls : List (Fin c.exports.length × List IVal)) : List (Fin c'.exports.length × List IVal) :=
  calls.map fun q => (Fin.cast h q.1, q.2)

/-- **The public component interaction equivalence**, on the reference machine only: the same
export types (export `i` of `c` and of `c'`), and for every typed sequence of calls and typed
last call, the same terminating observations (`seqObs`). Export names are not compared: the IR
calls exports by position. -/
structure RefPubEquiv (P : Profile) (prof : ProfileKind) (c c' : Simple) : Prop where
  len : c.exports.length = c'.exports.length
  ty : ∀ j : Fin c.exports.length, c'.exports[Fin.cast len j].ty = c.exports[j].ty
  obs : ∀ (calls : List (Fin c.exports.length × List IVal)) (j : Fin c.exports.length)
      (vs : List IVal), TypedCalls c calls → ValTy.checkList c.exports[j].ty.params vs = true →
    seqObs P prof c calls j vs = seqObs P prof c' (castCalls len calls) (Fin.cast len j) vs

/-! ## The IR side -/

/-- The play answering the export questions of the rounds `L` one after another (a round is a
question with its answer). -/
def exportRounds {k : Nat} :
    List (Σ q : (sigN k).Op, (sigN k).Ar q) → List (Move (sigN 0) (sigN k))
  | [] => []
  | ⟨q, a⟩ :: L => .inr (.ask q) :: .inr (.ans q a) :: exportRounds L

/-- A move at the export interface `sigN k`, read at the untyped interface `sigU`. -/
def forgetMove {k : Nat} : Move (sigN 0) (sigN k) → Move (sigN 0) sigU
  | .inl e => .inl e
  | .inr (.ask q) => .inr (.ask (q.1.val, q.2))
  | .inr (.ans q a) => .inr (.ans (q.1.val, q.2) a)

/-- The plays of a strategy at `sigN k`, read at `sigU`. -/
def pubPlays {k : Nat} (σ : Strategy (sigN 0) (sigN k)) : Set (List (Move (sigN 0) sigU)) :=
  {p | ∃ p' ∈ σ, p'.map forgetMove = p}

/-- No move follows a trap answer. -/
def TrapLast (p : List (Move (sigN 0) sigU)) : Prop :=
  ∀ l₁ l₂ (q : sigU.Op), p = l₁ ++ .inr (.ans q none) :: l₂ → l₂ = []

/-- **The trap-last plays** of a strategy, at `sigU`. -/
def trapLastPlays {k : Nat} (σ : Strategy (sigN 0) (sigN k)) : Set (List (Move (sigN 0) sigU)) :=
  {p | p ∈ pubPlays σ ∧ TrapLast p}

/-- The same export types, in order. -/
def SameTypes (c c' : Simple) : Prop := c.exports.map (·.ty) = c'.exports.map (·.ty)

/-- The fragment of the adequacy theorem: a float-free simple component within the flat
arities whose module is instantiated as the IR assumes. -/
structure Simple.Adequate (c : Simple) : Prop where
  good : c.Good
  floatFree : c.FloatFree
  inst : c.Inst
  arity : c.Arity

/-! ## A witness: the IR continues after a trap, the reference does not

Two components with the exports `poke: func() -> variant {}` and `peek: func() -> u32`. The
result type of `poke` is the empty variant: its lift traps on every discriminant, so every call
of `poke` traps after its core function has run.

* `pokePeekS`: `poke` runs `i32.const 1; global.set 0; i32.const 0` (it sets the global, then
  the lift traps) and `peek` runs `global.get 0`, over a mutable global initialised to `0`;
* `zeroS`: both exports run `i32.const 0`, over a module without global.

On the reference machine they are indistinguishable (`RefPubEquiv`): every call of `poke`
traps, and every resolved call of `peek` returns `0`, since after a trap nothing can be called.
Their IR strategies differ: `pokePeekS` plays `poke · trap · peek · 1`, which `zeroS` does not.
-/

/-- `(type (func (result i32)))`. -/
def resultI32 : List Silmaril.Wasm.RecType := [⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]

/-- `(global (mut i32) (i32.const 0)) (func (result i32) i32.const 1 global.set 0 i32.const 0)
(func (result i32) global.get 0) (export "set" (func 0)) (export "get" (func 1))`. -/
def pokePeekCore : Silmaril.Wasm.Module where
  types := resultI32
  globals := [⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 1, .globalSet ⟨0⟩, .intConst .i32 0]⟩,
    ⟨⟨0⟩, [], [.globalGet ⟨0⟩]⟩]
  exports := [⟨"set", .func ⟨0⟩⟩, ⟨"get", .func ⟨1⟩⟩]

/-- `(func (result i32) i32.const 0) (export "f" (func 0))`. -/
def zeroCore : Silmaril.Wasm.Module where
  types := resultI32
  funcs := [⟨⟨0⟩, [], [.intConst .i32 0]⟩]
  exports := [⟨"f", .func ⟨0⟩⟩]

/-- `poke` sets the global, then traps at the lift; `peek` reads the global. -/
def pokePeekS : Simple :=
  ⟨⟨pokePeekCore, [("set", ⟨[], [.int .i32]⟩), ("get", ⟨[], [.int .i32]⟩)]⟩,
    [⟨"poke", ⟨[], [.variant []]⟩, 0⟩, ⟨"peek", ⟨[], [.u32]⟩, 1⟩]⟩

/-- Both exports return `0` (`poke` then traps at the lift). -/
def zeroS : Simple :=
  ⟨⟨zeroCore, [("f", ⟨[], [.int .i32]⟩)]⟩,
    [⟨"poke", ⟨[], [.variant []]⟩, 0⟩, ⟨"peek", ⟨[], [.u32]⟩, 0⟩]⟩

end Silmaril.Wasm.Component.Reference
