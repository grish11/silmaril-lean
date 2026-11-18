module

public import Silmaril.Wasm.Component.InstSem.Defs
public import Silmaril.Wasm.Component.Param.Defs

/-!
# The game semantics of an engine instance with its instantiation phase

`Param.engineSem` (`Silmaril.Wasm.Component.Param`) gives a module with a start function the
strategy `trapAll`: `Param.instOf` has no instance when preparation reports a start function,
because the start-free interface `CoreSem` has no move at which the start function could run.
This module gives the engine semantics for the interface with an instantiation phase,
`CoreSemI` (`Silmaril.Wasm.Component.InstSem`), following the Wasm semantics and the reference
machine (`Reference.Instantiate`): the start function runs **at instantiation**, its import calls
are moves of the instantiation phase, a trap of it fails the instantiation, and only after a
successful instantiation are the exports served.

* `IInstance E`: an engine instance **before its start function**: the store `prepare?` returns,
  the export addresses, the start function's address (`none` when there is none).
* `instOfI E m imps exps`: as `Param.instOf`, keeping the start function.
* `engineLTSI E I imps exps`: the transition system, over `(sigN imps) ↠ (sigN exps).withInst
  Unit`, of the instance `I` (or of no instance, `I = none`). States `IState`:
  - `fresh`: before the question `inst`. Asked `inst`, the start thread `E.invoke a []` runs
    (`starting`); without a start function the instance is ready at once (`readying`); without
    an instance the instantiation fails (`failing`).
  - The start thread runs as an export call runs in `Param.engineStrategy`: a run of internal
    steps to a callout of host function `h` asks import `h` (`scall`), whose answer resumes it
    (`sret`); a run to returned values ends the instantiation (`sdone`, then `ready` answers
    `inst` with `ready`); a run to a trap fails it (`strap`, then `fail` answers `inst` with
    `fail ()`), after which nothing happens (`dead`).
  - **After instantiation the moves are those of `Param.engineStrategy`** (`ready x`, `lift`:
    the transitions `Param.ETrans` from the store left by the start function, export questions
    lifted to `some q`).
  Export calls before instantiation, a second `inst`, and anything after a failure are never
  answered.
* `engineStrategyI E I imps exps`: its strategy; `engineSemI E M emb : CoreSemI M` the core
  semantics with an instantiation phase given by an engine.
* `core3SemI P : CoreSemI ImpModule`: **the Core 3.0 instance** (`Reference.core3P P`, every
  profile), for modules with imports (`Reference.ImpModule`).

This is separate from the opt-in *lazy* start semantics proposed elsewhere (running the start
function at the first export call), which is not the specification's.

What is not modelled: divergence of the start function is silent (no move), which strategies
do not observe; the start function's returned values are not inspected (a validated start
function has type `[] → []`); a callout of a host function out of range, or a stuck thread, has
no move, as in `Param.engineStrategy`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Param

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine (CallResult Status)
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps)
open Silmaril.Wasm.Game (liftMove)

/-- An engine instance **before its start function**: the store after preparation, the function
address of each export, and the address of the start function (`none` when there is none). -/
structure IInstance (E : Engine) where
  /-- The store after preparation, before the start function. -/
  store : E.Store Nat
  /-- The function address of each export. -/
  addrs : List E.FuncAddr
  /-- The start function. -/
  start : Option E.FuncAddr

/-- The instance with its store and export addresses, forgetting the start function. -/
def IInstance.toE {E : Engine} (I : IInstance E) : EInstance E := ⟨I.store, I.addrs⟩

/-- **The engine instance of module `m` before its start function**: as `instOf`, keeping the
start function that `prepare?` reports. -/
def instOfI (E : Engine) (m : E.Module) (imps exps : CoreIface) : Option (IInstance E) :=
  let (s, as) := allocHosts E (E.empty Nat) 0 imps
  match E.prepare? s m (as.map E.ofFunc) with
  | some (s', inst, st) => (exportAddrs E inst exps).map fun addrs => ⟨s', addrs, st⟩
  | none => none

/-- Hidden states of the engine strategy with an instantiation phase. -/
inductive IState (E : Engine) (n k : Nat) where
  /-- Not yet asked to instantiate. -/
  | fresh
  /-- The start thread `t` runs at store `s`. -/
  | starting (s : E.Store Nat) (t : E.Thread Nat)
  /-- The start thread waits for the answer to the import question `e`. -/
  | startWait (s : E.Store Nat) (t : E.Thread Nat) (e : (sigN n).Op)
  /-- Instantiation succeeded at store `s`; `inst` is about to be answered `ready`. -/
  | readying (s : E.Store Nat)
  /-- Instantiation failed; `inst` is about to be answered `fail ()`. -/
  | failing
  /-- Instantiation failed: nothing else happens. -/
  | dead
  /-- After instantiation: the states of `engineStrategy`. -/
  | ready (x : EState E n k)

/-- The export addresses of an optional instance. -/
def addrsOf {E : Engine} (I : Option (IInstance E)) : List E.FuncAddr :=
  (I.map IInstance.addrs).getD []

/-- The transitions of an engine instance with its instantiation phase (labels `none` are
silent). -/
inductive ITrans (E : Engine) (I : Option (IInstance E)) (imps exps : CoreIface) :
    IState E imps.length exps.length →
      Option (Move (sigN imps.length) ((sigN exps.length).withInst Unit)) →
      IState E imps.length exps.length → Prop where
  /-- `inst` runs the start function (Opponent). -/
  | start {J : IInstance E} {a : E.FuncAddr} (hI : I = some J) (ha : J.start = some a) :
      ITrans E I imps exps .fresh (some askInst) (.starting J.store (E.invoke a []))
  /-- `inst` of an instance without a start function (Opponent). -/
  | noStart {J : IInstance E} (hI : I = some J) (ha : J.start = none) :
      ITrans E I imps exps .fresh (some askInst) (.readying J.store)
  /-- `inst` without an instance (Opponent). -/
  | noInst (hI : I = none) : ITrans E I imps exps .fresh (some askInst) .failing
  /-- A run of the start thread to a callout of host function `h` asks import `h`
  (Proponent). -/
  | scall {s s' : E.Store Nat} {t t' : E.Thread Nat} {h : Nat} {args : List Flat}
      (run : Steps E (s, t) (s', t')) (callout : E.status s' t' = .callout h args)
      (hh : h < imps.length) :
      ITrans E I imps exps (.starting s t) (some (.inl (.ask (⟨h, hh⟩, .flat args))))
        (.startWait s' t' (⟨h, hh⟩, .flat args))
  /-- The answer to the import call resumes the start thread (Opponent). -/
  | sret {s : E.Store Nat} {t : E.Thread Nat} {e : (sigN imps.length).Op} (r : Option Payload) :
      ITrans E I imps exps (.startWait s t e) (some (.inl (.ans e r)))
        (.starting s (E.resume s t (resultOf imps[e.1].2.results r)))
  /-- A run of the start thread to returned values: instantiation succeeds (silent). -/
  | sdone {s s' : E.Store Nat} {t t' : E.Thread Nat} {ys : List Flat}
      (run : Steps E (s, t) (s', t')) (final : E.status s' t' = .returned (.values ys)) :
      ITrans E I imps exps (.starting s t) none (.readying s')
  /-- A run of the start thread to a trap: instantiation fails (silent). -/
  | strap {s s' : E.Store Nat} {t t' : E.Thread Nat}
      (run : Steps E (s, t) (s', t')) (final : E.status s' t' = .returned .trap) :
      ITrans E I imps exps (.starting s t) none .failing
  /-- `inst` is answered `ready`; the exports are now served from the store (Proponent). -/
  | ready {s : E.Store Nat} :
      ITrans E I imps exps (.readying s) (some (ansInst .ready)) (.ready (.idle s))
  /-- `inst` is answered `fail ()` (Proponent). -/
  | fail : ITrans E I imps exps .failing (some (ansInst (.fail ()))) .dead
  /-- After instantiation, the moves of `engineStrategy`, export questions lifted. -/
  | lift {x y : EState E imps.length exps.length}
      {m : Move (sigN imps.length) (sigN exps.length)} (h : ETrans E (addrsOf I) imps exps x m y) :
      ITrans E I imps exps (.ready x) (some (liftMove m)) (.ready y)

/-- The transition system of an engine instance with its instantiation phase. -/
def engineLTSI (E : Engine) (I : Option (IInstance E)) (imps exps : CoreIface) :
    LTS (sigN imps.length) ((sigN exps.length).withInst Unit) where
  State := IState E imps.length exps.length
  init := .fresh
  step := ITrans E I imps exps

/-- **The game semantics of an engine instance with its instantiation phase.** -/
def engineStrategyI (E : Engine) (I : Option (IInstance E)) (imps exps : CoreIface) :
    Strategy (sigN imps.length) ((sigN exps.length).withInst Unit) :=
  Strategy.ofLTS (engineLTSI E I imps exps)

/-- **A run of the start phase** from `c` to `c'` whose import calls (with their answers) are
`cs`: runs of internal steps, each but the last ending at a callout of an import, answered and
resumed. -/
inductive StartRunI (E : Engine) (imps : CoreIface) :
    E.Config Nat → List (Σ _ : (sigN imps.length).Op, Option Payload) → E.Config Nat → Prop where
  /-- A run of internal steps. -/
  | nil {c c' : E.Config Nat} (run : Steps E c c') : StartRunI E imps c [] c'
  /-- A run to a callout of import `h`, the answer `r`, then the rest of the start phase. -/
  | call {s s' : E.Store Nat} {t t' : E.Thread Nat} {h : Nat} {args : List Flat}
      {c'' : E.Config Nat} {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
      (run : Steps E (s, t) (s', t')) (callout : E.status s' t' = .callout h args)
      (hh : h < imps.length) (r : Option Payload)
      (rest : StartRunI E imps (s', E.resume s' t' (resultOf imps[h].2.results r)) cs c'') :
      StartRunI E imps (s, t) (⟨(⟨h, hh⟩, .flat args), r⟩ :: cs) c''

/-- **The core semantics with an instantiation phase given by an engine**: each module denotes
the game semantics of its instance before its start function (through `emb`); the start
function runs at instantiation. -/
def engineSemI (E : Engine) (M : Type) [CoreModule M] (emb : M → E.Module) : CoreSemI M where
  sem m := engineStrategyI E (instOfI E (emb m) (CoreModule.imports m) (CoreModule.exports m))
    (CoreModule.imports m) (CoreModule.exports m)

/-- **The Core 3.0 core semantics with an instantiation phase**, at profile `P`, for modules with
imports: start functions run at instantiation. -/
noncomputable def core3SemI (P : Silmaril.Wasm.Numerics.Profile) : CoreSemI ImpModule :=
  engineSemI (core3P P) ImpModule ImpModule.mod

end Silmaril.Wasm.Component.Param
