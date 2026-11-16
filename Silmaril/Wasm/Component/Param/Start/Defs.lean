module

public import Silmaril.Wasm.Component.Param.Defs

/-!
# The game semantics of an engine instance with a start function

`Param.instOf` has no instance for a module whose preparation reports a start function, so
`Param.engineSem` gives such a module the strategy trapping on every question (`trapAll`).
That is not the Wasm semantics: the start function runs during instantiation, after the
segments are initialised (Wasm 3.0 spec, "Instantiation"); its import calls are calls of the
environment like any other, a trap of the start function makes instantiation fail, and only
then are the exports available. The reference machine does the same
(`Reference.Instantiate.instantiateCore`, `runStart`: the start function is called during core
instantiation; a trap of it is a trap of the instantiation).

This module gives a **lazy** start-aware semantics. It is an approximation that **deviates from
that semantics** (the start phase runs at the first export question; see "Where the start phase
is observed" below), and it is opt-in: `Binary.coreModSemLazyStart` uses it, the default
`Binary.coreModSem` does not. A faithful treatment needs an instantiation phase in the IR's
interface (as in `Silmaril.Wasm.Game.Start`), which `CoreSem` does not have.

* `SInstance E`: an engine instance **before its start function**: the store `prepare?` returns,
  the export addresses, and the start function's address (`none` when there is none).
* `instOfS E m imps exps`: as `instOf`, keeping the start function instead of discarding the
  module.
* `engineLTSS E I imps exps` and `engineStrategyS E I imps exps`: the strategy of the instance
  with its start phase. The states are `SState`:
  - `pending s t`: the start function has not run; `t` is its invocation `E.invoke a []`.
  - At the **first export question** `q`, of any type, the start thread runs (`starting q s t`).
    A run of internal steps to a callout of host function `h` asks import `h` (`scall`,
    `startWait`), and the answer resumes it (`sret`), as for an export call (`ETrans.ucall`,
    `ETrans.uret`). A run to returned values ends the start phase (`sdone`), and `q` is served
    from the resulting store exactly as `engineStrategy` serves it from `idle` (`dispatch`:
    invoke the export, or refuse an ill-typed question). A run to a trap fails the
    instantiation (`strap`): `q` is answered by a trap, and so is every later question
    (`failing`, `failed`).
  - After the start phase the states are those of `engineStrategy` (`ready`).
  Without a start function the initial state is `ready (idle s)`, so the strategy is
  `engineStrategy` (`engineStrategyS_of_start_none`, `Param.Start.Thms`).
* `engineSemS E M emb : CoreSem M`: each module denotes the strategy of its instance with its
  start phase, and traps on every question when it has no instance. It agrees with
  `engineSem` on every module without a start function (`engineSemS_sem_of_noStart`).
* `StartRun E imps c w c'`: a run of the start thread from `c` to `c'` whose import calls and
  answers are the moves `w` (used to state what the start phase does).

## Where the start phase is observed

The component IR's plays begin with an export question, and its core instances are lazy: "an
instance does nothing until it is called" (`Silmaril.Wasm.Component.Semantics`). There is no
instantiation move in `CoreSem` (unlike `Silmaril.Wasm.Game.Start`, whose signature
`F.withInst` has one). The start phase is therefore run **at the first export question, before
it is served**: the start function's import calls are import questions nested in that first
question. This is the only place in the IR's protocol where they can be observed. Compared to
the spec and the reference machine:

* the start function's effects and import calls happen at the first call of the instance,
  not at its instantiation; an instance that is never called never runs its start function.
  Within one instance, the order is the spec's: the whole start phase precedes every export
  call. Across instances, start phases run in the order of the instances' first calls, not in
  instantiation order.
* a trap of the start function makes every question of the instance trap (the instance is
  unusable), where the spec aborts the whole instantiation. The reference IR does the same
  (`Reference.modSemS` traps on every question when the start phase may fail).
* divergence of the start function is silent divergence (no further move), which strategies do
  not observe (`Silmaril.Games.Strategy`).
* the start function's returned values are not inspected (a validated start function has type
  `[] → []`).
* a start-phase callout of a host function out of range, or a stuck start thread, has no
  move, as in `engineStrategy`.

The reference semantics `Reference.modSemS` (import-free modules) and `Reference.impSemS`
(modules with imports whose start function makes no import call, `ImpModule.StartNoCall`) run
the start phase **eagerly and in a closed world** and take the strategy of the instance at
every store where it may return. They cannot show import calls of the start function.
`engineSemS` does not need that hypothesis.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Param

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine (CallResult Status)
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps)

/-- An engine instance **before its start function**: the store after preparation, the function
address of each export, and the address of the start function (`none` when there is none). -/
structure SInstance (E : Engine) where
  /-- The store after preparation, before the start function. -/
  store : E.Store Nat
  /-- The function address of each export. -/
  addrs : List E.FuncAddr
  /-- The start function. -/
  start : Option E.FuncAddr

/-- The instance with its store and export addresses, forgetting the start function. -/
def SInstance.toE {E : Engine} (I : SInstance E) : EInstance E := ⟨I.store, I.addrs⟩

/-- **The engine instance of module `m` before its start function**: as `instOf`, keeping the
start function that `prepare?` reports. -/
def instOfS (E : Engine) (m : E.Module) (imps exps : CoreIface) : Option (SInstance E) :=
  let (s, as) := allocHosts E (E.empty Nat) 0 imps
  match E.prepare? s m (as.map E.ofFunc) with
  | some (s', inst, st) => (exportAddrs E inst exps).map fun addrs => ⟨s', addrs, st⟩
  | none => none

/-- The state of `engineStrategy` right after the export question `q` at store `s`: the
export's invocation, or a refusal of an ill-typed question (`ETrans.call`, `ETrans.refuse`). -/
def dispatch {E : Engine} {n : Nat} (addrs : List E.FuncAddr) (exps : CoreIface)
    (q : (sigN exps.length).Op) (s : E.Store Nat) : EState E n exps.length :=
  match callee? addrs exps q with
  | some (a, xs) => .running q s (E.invoke a xs)
  | none => .refusing q s

/-- Hidden states of the engine strategy with a start phase. -/
inductive SState (E : Engine) (n k : Nat) where
  /-- The start function has not run; `t` is its invocation at store `s`. -/
  | pending (s : E.Store Nat) (t : E.Thread Nat)
  /-- The start thread `t` runs, on behalf of the first question `q`. -/
  | starting (q : (sigN k).Op) (s : E.Store Nat) (t : E.Thread Nat)
  /-- The start thread waits for the answer to the import question `e`. -/
  | startWait (q : (sigN k).Op) (s : E.Store Nat) (t : E.Thread Nat) (e : (sigN n).Op)
  /-- The start function trapped: `q` is about to be answered by a trap. -/
  | failing (q : (sigN k).Op)
  /-- The start function trapped: the instance is unusable. -/
  | failed
  /-- The start phase is over: the states of `engineStrategy`. -/
  | ready (x : EState E n k)

/-- The transitions of an engine instance with a start phase (labels `none` are silent). -/
inductive STrans (E : Engine) (addrs : List E.FuncAddr) (imps exps : CoreIface) :
    SState E imps.length exps.length → Option (Move (sigN imps.length) (sigN exps.length)) →
      SState E imps.length exps.length → Prop where
  /-- The first export question starts the start function (Opponent). -/
  | first {s : E.Store Nat} {t : E.Thread Nat} {q : (sigN exps.length).Op} :
      STrans E addrs imps exps (.pending s t) (some (.inr (.ask q))) (.starting q s t)
  /-- A run of the start thread to a callout of host function `h` asks import `h`
  (Proponent). -/
  | scall {q : (sigN exps.length).Op} {s s' : E.Store Nat} {t t' : E.Thread Nat} {h : Nat}
      {args : List Flat} (run : Steps E (s, t) (s', t'))
      (callout : E.status s' t' = .callout h args) (hh : h < imps.length) :
      STrans E addrs imps exps (.starting q s t) (some (.inl (.ask (⟨h, hh⟩, .flat args))))
        (.startWait q s' t' (⟨h, hh⟩, .flat args))
  /-- The answer to the import call resumes the start thread (Opponent). -/
  | sret {q : (sigN exps.length).Op} {s : E.Store Nat} {t : E.Thread Nat}
      {e : (sigN imps.length).Op} (r : Option Payload) :
      STrans E addrs imps exps (.startWait q s t e) (some (.inl (.ans e r)))
        (.starting q s (E.resume s t (resultOf imps[e.1].2.results r)))
  /-- A run of the start thread to returned values ends the start phase; the first question
  is then served as `engineStrategy` serves it (silent). -/
  | sdone {q : (sigN exps.length).Op} {s s' : E.Store Nat} {t t' : E.Thread Nat}
      {ys : List Flat} (run : Steps E (s, t) (s', t'))
      (final : E.status s' t' = .returned (.values ys)) :
      STrans E addrs imps exps (.starting q s t) none (.ready (dispatch addrs exps q s'))
  /-- A run of the start thread to a trap fails the instantiation (silent). -/
  | strap {q : (sigN exps.length).Op} {s s' : E.Store Nat} {t t' : E.Thread Nat}
      (run : Steps E (s, t) (s', t')) (final : E.status s' t' = .returned .trap) :
      STrans E addrs imps exps (.starting q s t) none (.failing q)
  /-- After a failed start, the question is answered by a trap (Proponent). -/
  | fail {q : (sigN exps.length).Op} :
      STrans E addrs imps exps (.failing q) (some (.inr (.ans q none))) .failed
  /-- After a failed start, every question is answered by a trap (Opponent). -/
  | dead {q : (sigN exps.length).Op} :
      STrans E addrs imps exps .failed (some (.inr (.ask q))) (.failing q)
  /-- After the start phase, the moves of `engineStrategy`. -/
  | lift {x y : EState E imps.length exps.length} {m : Move (sigN imps.length) (sigN exps.length)}
      (h : ETrans E addrs imps exps x m y) :
      STrans E addrs imps exps (.ready x) (some m) (.ready y)

/-- The initial state: the pending start function, or `engineStrategy`'s initial state when
there is none. -/
def SInstance.init {E : Engine} {n k : Nat} (I : SInstance E) : SState E n k :=
  match I.start with
  | none => .ready (.idle I.store)
  | some a => .pending I.store (E.invoke a [])

/-- The transition system of an engine instance with its start phase. -/
def engineLTSS (E : Engine) (I : SInstance E) (imps exps : CoreIface) :
    LTS (sigN imps.length) (sigN exps.length) where
  State := SState E imps.length exps.length
  init := I.init
  step := STrans E I.addrs imps exps

/-- **The game semantics of an engine instance with its start phase.** -/
def engineStrategyS (E : Engine) (I : SInstance E) (imps exps : CoreIface) :
    Strategy (sigN imps.length) (sigN exps.length) :=
  Strategy.ofLTS (engineLTSS E I imps exps)

/-- **The core semantics of the IR given by an engine, start functions included**: each module
denotes the game semantics of its instance with its start phase (through `emb`), and traps on
every question when it has none. -/
def engineSemS (E : Engine) (M : Type) [CoreModule M] (emb : M → E.Module) : CoreSem M where
  sem m :=
    match instOfS E (emb m) (CoreModule.imports m) (CoreModule.exports m) with
    | some I => engineStrategyS E I (CoreModule.imports m) (CoreModule.exports m)
    | none => trapAll _ _

/-- **A run of the start phase** from `c` to `c'` whose import calls and answers are `w`: runs
of internal steps, each but the last ending at a callout of an import, answered with `r` and
resumed. -/
inductive StartRun (E : Engine) (imps : CoreIface) {k : Nat} :
    E.Config Nat → List (Move (sigN imps.length) (sigN k)) → E.Config Nat → Prop where
  /-- A run of internal steps. -/
  | nil {c c' : E.Config Nat} (run : Steps E c c') : StartRun E imps c [] c'
  /-- A run to a callout of import `h`, the answer `r`, then the rest of the start phase. -/
  | call {s s' : E.Store Nat} {t t' : E.Thread Nat} {h : Nat} {args : List Flat}
      {c'' : E.Config Nat} {w : List (Move (sigN imps.length) (sigN k))}
      (run : Steps E (s, t) (s', t')) (callout : E.status s' t' = .callout h args)
      (hh : h < imps.length) (r : Option Payload)
      (rest : StartRun E imps (s', E.resume s' t' (resultOf imps[h].2.results r)) w c'') :
      StartRun E imps (s, t)
        (.inl (.ask (⟨h, hh⟩, .flat args)) :: .inl (.ans (⟨h, hh⟩, .flat args) r) :: w) c''

end Silmaril.Wasm.Component.Param
