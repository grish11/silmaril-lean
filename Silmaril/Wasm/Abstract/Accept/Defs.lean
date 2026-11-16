module

public import Silmaril.Games.Abstract.Machine.Defs
public import Silmaril.Games.Abstract.Function.Defs
public import Silmaril.Games.Accept.Defs
public import Silmaril.Semantics.Accept.Verdict.Defs
public import Silmaril.Semantics.Accept.Rel.Defs

/-! # Acceptor sets of abstract modules and components

The acceptance readings of `Silmaril.Wasm.Game.Accept` and `Silmaril.Wasi.Component.Accept`,
stated for the **abstract** semantics of `Silmaril.Games.Abstract`:

* **Trace models and machines** (`TraceModel G`, `Machine G`): abstract instances, modules and
  components as sets of plays of a game `G`.
  * `tmAccepted T obs` / `mAccepted M obs`: the values a move observation `obs` reads in some
    play. Over a machine, only its legal traces count.
  * `tmRun T val`: the **runner** sending a value to the moves carrying it (`val`) in some
    play. `tmAcceptsSome`, `tmNeverRejects` and `tmAcceptsSafely` instantiate the generic
    verdicts of `Silmaril.Semantics.Accept` with this one runner, for accepting moves `acc` and
    rejecting moves `rej`. Some play accepts, no play rejects, or both, over the **same** plays.
  * `tmIndexed T val`: one acceptor set per index (an import, an export), as a
    `Silmaril.Accept.IndexedLang`.
* **Abstract functions** (`AFun E S A B`: a state and an argument give a set of call behaviours,
  the import calls made and how the call ended), over a set `D` of admitted initial states:
  * `endRun f D a`: the endings of the calls on `a` from a state of `D`. `retAcceptsSome`,
    `retNeverRejects` and `retAcceptsSafely` are the export readings (`accept(a)` returns an
    accepting ending), all with this runner.
  * `callAccepted f D obs`: the values an import-call observation reads in some behaviour (the
    import reading).
  * `callRel f D obs`: the relational form, input `a` ↦ observed value `v`, scoped to one
    invocation (a call behaviour is the behaviour of one call, so the scoping is exact, not an
    assumption).

The concrete-to-abstract diagrams are in `Silmaril.Wasm.Abstract.Accept.Thms`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.Accept

open Silmaril.Games Silmaril.Games.Abstract
open scoped SetRel Silmaril.Accept

universe u v

/-! ## Trace models and machines -/

section TraceModels

variable {G : Game.{u}} {α : Type v}

/-- The values `obs` reads at some move of some play of `T`. -/
def tmAccepted (T : TraceModel G) (obs : G.Move → Option α) : Set α :=
  Silmaril.Games.Accept.observed obs T.plays

/-- The values `obs` reads at some move of some legal trace of `M`. -/
def mAccepted (M : Machine G) (obs : G.Move → Option α) : Set α :=
  Silmaril.Games.Accept.observed obs (M.traces ∩ G.Legal)

/-- **The runner of a trace model**: the moves carrying a value in some play. -/
def tmRun (T : TraceModel G) (val : G.Move → Option α) (a : α) : Set G.Move :=
  {m | (∃ s ∈ T.plays, m ∈ s) ∧ val m = some a}

/-- Some play has an accepting move carrying the value. -/
def tmAcceptsSome (T : TraceModel G) (val : G.Move → Option α) (acc : Set G.Move) : Set α :=
  Silmaril.Accept.acceptsSome (tmRun T val) acc

/-- No play has a rejecting move carrying the value. -/
def tmNeverRejects (T : TraceModel G) (val : G.Move → Option α) (rej : Set G.Move) : Set α :=
  Silmaril.Accept.neverRejects (tmRun T val) rej

/-- Some play accepts and no play rejects, over the same plays. -/
def tmAcceptsSafely (T : TraceModel G) (val : G.Move → Option α) (acc rej : Set G.Move) :
    Set α :=
  Silmaril.Accept.acceptsSafely (tmRun T val) acc rej

/-- One acceptor set per index. -/
def tmIndexed {ι : Type v} (T : TraceModel G) (val : ι → G.Move → Option α) :
    Silmaril.Accept.IndexedLang (fun _ : ι => α) :=
  fun i => tmAccepted T (val i)

/-- An observation restricted to the moves of `acc`. -/
def restrictObs (val : G.Move → Option α) (acc : Set G.Move) [DecidablePred (· ∈ acc)] :
    G.Move → Option α :=
  fun m => if m ∈ acc then val m else none

end TraceModels

/-! ## Abstract functions -/

section Functions

variable {E : Sig.{u}} {S A B : Type u} {α : Type u}

/-- **The runner of an abstract function**: the endings of the calls on `a` from an admitted
state. -/
def endRun (f : AFun E S A B) (D : Set S) (a : A) : Set (End S B) :=
  {e | ∃ s ∈ D, ∃ x ∈ f s a, x.2 = e}

/-- Export reading: some call on the argument ends in `acc`. -/
def retAcceptsSome (f : AFun E S A B) (D : Set S) (acc : Set (End S B)) : Set A :=
  Silmaril.Accept.acceptsSome (endRun f D) acc

/-- No call on the argument ends in `rej`. -/
def retNeverRejects (f : AFun E S A B) (D : Set S) (rej : Set (End S B)) : Set A :=
  Silmaril.Accept.neverRejects (endRun f D) rej

/-- Some call ends in `acc`, no call ends in `rej`. -/
def retAcceptsSafely (f : AFun E S A B) (D : Set S) (acc rej : Set (End S B)) : Set A :=
  Silmaril.Accept.acceptsSafely (endRun f D) acc rej

/-- Import reading: the values an import-call observation reads in some behaviour. -/
def callAccepted (f : AFun E S A B) (D : Set (S × A)) (obs : Call E → Option α) : Set α :=
  {v | ∃ i ∈ D, ∃ x ∈ f i.1 i.2, ∃ c ∈ x.1, obs c = some v}

/-- **The relational form**: the argument of one invocation, and a value observed among the
import calls of that same invocation. -/
def callRel (f : AFun E S A B) (D : Set S) (obs : Call E → Option α) : A -|> α :=
  {p | ∃ s ∈ D, ∃ x ∈ f s p.1, ∃ c ∈ x.1, obs c = some p.2}

end Functions

end Silmaril.Wasm.Abstract.Accept
