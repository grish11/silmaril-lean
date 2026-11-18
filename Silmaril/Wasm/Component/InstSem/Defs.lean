module

public import Silmaril.Wasm.Component.Semantics.Defs
public import Silmaril.Games.Inst.Defs
public import Silmaril.Wasm.Game.Start.Defs

/-!
# The component IR with an instantiation phase

`Comp.denU` (`Silmaril.Wasm.Component.Semantics`) has no instantiation move: a core instance's
strategy starts with an export question, so start functions and instantiation-time effects are
not modelled. This module gives the IR a denotation in which **instantiation is a move**, using
the instantiation signature `F.withInst R` of `Silmaril.Games.Inst`: an extra question `inst`
(`none`), answered `ready` or `fail r`, before the export calls `some q`.

## Core semantics with an instantiation phase

`CoreSemI M` gives each core module a strategy over `(sig imports) ↠ (sig exports).withInst Unit`.
Its first phase answers `inst`, possibly calling imports on the way (a start function's import
calls are moves of that phase), with `ready` or `fail ()` (a trap of the start function, or no
instance); export calls follow. The failure outcome is `Unit`: a failed instantiation is a trap.

`CoreSem.toI C : CoreSemI M` is the adapter from the start-free interface: each module answers
`inst` with `ready` at once (`withReady`), then behaves as `C.sem m`.

## Combinators

* `readyH F R : Handler F (F.withInst R)`: `inst` is answered `ready`, exports are forwarded;
  `withReady σ = σ ≫ readyH`.
* `exH F R : Handler (F.withInst R) F`: calls of `F` as export calls of an instantiable `F`.
* `liftH h : Handler (E.withInst R) (F.withInst R)`: `inst` is forwarded, an export is the
  program `h q` with its calls made export calls (`exH`). Wiring handlers (`implsN`, `widenH`,
  `exportsH`) act on the export phase through `liftH`.
* `instSplitH e : Handler (sigUI ⊕ₛ sigUI) sigUI` (`sigUI = sigU.withInst Unit`): **instantiation
  in order**. `inst` instantiates the left side (the environment); if it fails, the failure is
  the answer and the right side (the new instance) is never asked; if it is ready, the right
  side is instantiated and its answer is the answer. Export calls are split at `e` (`splitH`).
* `extI e D N` (the analogue of `ext`): the environment `D` of `e` functions extended by the
  instance `N`, whose import calls are export calls of `D` (made after `D` is ready):
  `D ≫ ((id).pair (exH ≫ N) ≫ instSplitH e)`.

## The denotation

`Comp.denIR C c : Strategy sigU sigUI` follows `Comp.denU` node by node: the imports are ready at
once (`withReady (maskH …)`), each node extends the environment by `extI`, a core node is
`implsN ≫ C.sem m ≫ liftH widenH`, a nested component is `implsH ≫ denIR`, and the exports are
`liftH (exportsH …)` (which forwards `inst`). So instantiating a component instantiates its
nodes **in program order**, each start function's import calls are moves at that time, and the
first failure aborts the instantiation: later nodes are never instantiated. A node is
instantiated whether or not anything ever calls it.

The handlers are stateless, so `denIR` would also forward a second `inst`, or an export call
before instantiation. **The protocol** is imposed once, at the outermost level:
`Comp.denI C c = instGuard (Comp.denIR C c)` keeps the plays whose upper moves are `inst`
first, then export calls only after `ready`, and nothing after `fail` (`InstProper`); any other
Opponent question is accepted and never answered. In particular after a failed instantiation no
export is callable.

## Observations

* `instPlay cs a`: the instantiation play `inst`, the complete calls `cs` below, the answer `a`;
* `lowerAsks p`: the calls made below in the play `p`, in order.

The comparison with `Comp.denU` (`denIR_toI`, `denI_toI_iff`: after `[inst, ready]`, lifted by
`Wasm.Game.liftMove`, the plays are those of `Comp.denU`) is in `InstSem.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games Silmaril.Games.Inst
open Silmaril.Wasm.Game (liftMove liftEv)

/-! ## Instantiation combinators -/

/-- `inst` is answered `ready` at once; export calls are forwarded. -/
def readyH (F : Sig.{0}) (R : Type) : Handler F (F.withInst R) := fun q =>
  match q with
  | none => .pure InstAns.ready
  | some q => .call q fun n => .pure n

/-- The export calls of an instantiable `F`, as a renaming. -/
def exHom (F : Sig.{0}) (R : Type) : Sig.Hom F (F.withInst R) := ⟨some, fun _ n => n⟩

/-- Calls of `F` as export calls of an instantiable `F`. -/
abbrev exH (F : Sig.{0}) (R : Type) : Handler (F.withInst R) F := Handler.ofHom (exHom F R)

/-- A wiring handler acting on the export phase: `inst` is forwarded, an export call runs `h`,
whose calls are export calls below. -/
def liftH {E F : Sig.{0}} {R : Type} (h : Handler E F) : Handler (E.withInst R) (F.withInst R) :=
  fun q =>
    match q with
    | none => .call none fun n => .pure n
    | some q => (h q).interp (exH E R)

/-- A start-free strategy as an instantiable one: `inst` is answered `ready` at once. -/
def withReady {E F : Sig.{0}} {R : Type} (σ : Strategy E F) : Strategy E (F.withInst R) :=
  σ.comp (Strategy.ofHandler (readyH F R))

/-- **An instantiation play**: `inst`, the complete calls `cs` below (each question with its
answer), then the answer `a`. -/
def instPlay {E F : Sig.{0}} {R : Type} (cs : List (Σ m : E.Op, E.Ar m)) (a : InstAns R) :
    List (Move E (F.withInst R)) :=
  askInst :: (cs.flatMap fun c => [.inl (.ask c.1), .inl (.ans c.1 c.2)]) ++ [ansInst a]

/-- The calls made below in a play, in order. -/
def lowerAsks {E F : Sig.{0}} : List (Move E F) → List E.Op
  | [] => []
  | .inl (.ask m) :: p => m :: lowerAsks p
  | _ :: p => lowerAsks p

/-! ## The protocol -/

/-- An event of an instantiable interface concerns an export call. -/
def IsExEv {F : Sig.{0}} {R : Type} : Ev (F.withInst R) → Prop
  | .ask m => m.isSome
  | .ans m _ => m.isSome

/-- **The instantiation protocol** on the upper events: `inst` first; then, after `ready`,
export events only; nothing after `fail`. -/
def ProperUp {F : Sig.{0}} {R : Type} (u : List (Ev (F.withInst R))) : Prop :=
  u = [] ∨ u = [.ask none] ∨ (∃ r, u = [.ask none, Ev.ans (E := F.withInst R) none (.fail r)]) ∨
    ∃ rest, u = .ask none :: Ev.ans (E := F.withInst R) none .ready :: rest ∧ ∀ x ∈ rest, IsExEv x

/-- A play follows the instantiation protocol. -/
def InstProper {E F : Sig.{0}} {R : Type} (p : List (Move E (F.withInst R))) : Prop :=
  ProperUp (upper p)

/-- **The protocol guard**: the plays of `σ` that follow the instantiation protocol; any other
Opponent question is accepted and never answered. -/
def instGuard {E F : Sig.{0}} {R : Type} (σ : Strategy E (F.withInst R)) :
    Strategy E (F.withInst R) :=
  Strategy.generate {p | p ∈ σ ∧ InstProper p}

/-! ## Instantiation in program order -/

/-- The universal instantiable interface; a failed instantiation is a trap (`fail ()`). -/
abbrev sigUI : Sig.{0} := sigU.withInst Unit

/-- **Instantiation in order, exports split at `e`**: `inst` instantiates the left side, and only
if it is ready the right side, whose answer is the answer; a failure of the left side is the
answer. Export calls below `e` go left, the others right (shifted by `e`). -/
def instSplitH (e : Nat) : Handler (sigUI ⊕ₛ sigUI) sigUI := fun q =>
  match q with
  | none => .call (.inl none) fun (a : InstAns Unit) =>
      match a with
      | .ready => .call (.inr none) fun (b : InstAns Unit) => .pure b
      | .fail r => .pure (.fail r)
  | some q =>
    if q.1 < e then .call (.inl (some q)) fun n => .pure n
    else .call (.inr (some (q.1 - e, q.2))) fun n => .pure n

/-- **Extend the instantiable environment `D` (of `e` functions) by the instance `N`**: one
instance `D`, shared by the forwarding copycat and by `N`, whose import calls are export calls
of `D`; instantiation instantiates `D`, then `N`. -/
def extI {X : Sig.{0}} (e : Nat) (D : Strategy X sigUI) (N : Strategy sigU sigUI) :
    Strategy X sigUI :=
  D.comp (((Strategy.id sigUI).pair ((Strategy.ofHandler (exH sigU Unit)).comp N)).comp
    (Strategy.ofHandler (instSplitH e)))

variable {M : Type} [CoreModule M]

/-- **A semantics of core modules with an instantiation phase**: for each module, a strategy over
its flat imports and its flat exports with an instantiation question. -/
structure CoreSemI (M : Type) [CoreModule M] where
  /-- The strategy of a core module, instantiation first. -/
  sem : (m : M) → Strategy (CoreIface.sig (CoreModule.imports m))
    ((CoreIface.sig (CoreModule.exports m)).withInst Unit)

/-- **The adapter from start-free core semantics**: instantiation is `ready` at once. -/
def CoreSem.toI (C : CoreSem M) : CoreSemI M where
  sem m := withReady (C.sem m)

/-- A core instance of `m` with the wiring `args`, with its instantiation phase. -/
def coreNodeI (C : CoreSemI M) (e : Nat) (m : M) (args : List Impl) : Strategy sigU sigUI :=
  (Strategy.ofHandler (implsN e args (CoreModule.imports m).length)).comp
    ((C.sem m).comp (Strategy.ofHandler (liftH (widenH (CoreModule.exports m).length))))

mutual
/-- **The strategy of a component with its instantiation phase**, over `sigU` (no protocol
guard; see `Comp.denI`). -/
def Comp.denIR (C : CoreSemI M) : Comp M → Strategy sigU sigUI
  | .mk I ns xs =>
    (denNodesI C I.length ns (withReady (Strategy.ofHandler (maskH I.length)))).comp
      (Strategy.ofHandler (liftH (exportsH (envAfter I.length ns) xs)))

/-- Extend the instantiable environment `D` (of `e` functions) by the nodes `ns`, in order. -/
def denNodesI (C : CoreSemI M) {X : Sig.{0}} : Nat → List (Node M) → Strategy X sigUI →
    Strategy X sigUI
  | _, [], D => D
  | e, n :: ns, D => denNodesI C (e + n.width) ns (extI e D (Node.denI C e n))

/-- The strategy of a node with its instantiation phase, over an environment of `e`
functions. -/
def Node.denI (C : CoreSemI M) : Nat → Node M → Strategy sigU sigUI
  | e, .core m args => coreNodeI C e m args
  | e, .inst c args => (Strategy.ofHandler (implsH e args)).comp (Comp.denIR C c)
end

/-- **The strategy of a component with its instantiation phase**: `Comp.denIR` under the
instantiation protocol (`instGuard`). -/
def Comp.denI (C : CoreSemI M) (c : Comp M) : Strategy sigU sigUI :=
  instGuard (c.denIR C)

end Silmaril.Wasm.Component
