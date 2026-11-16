module

public import Silmaril.Containers.Precondition.Defs
public import Silmaril.Semantics.Acceptors.Defs
public import Silmaril.Semantics.Accept.Defs
public import Silmaril.Logic.Consequence.Defs

/-!
# Container obligations as consequence systems and acceptors

This module states container obligations in the two shapes the library already has for checked
judgements, so that container checks are recorded and compared like the others
(`docs/projects/consequence-systems.md`, `docs/accept.md`).

**Consequence systems** (`Silmaril.Consequence.System Ax C := Ax → C → Prop`). Contexts are images,
conclusions are specifications of runs:

* `vsys R`: `i ⊢ φ` iff `vpre R φ i`: every run of `i` under the runtime model `R` has **no
  undefined behaviour** and satisfies `φ`. This is the system checked obligations are judged in;
* `rawsys R`: `i ⊢ φ` iff `pre R φ i`, raw satisfaction. It is kept only as a comparison: it is not
  sound for `vsys` (`Silmaril.Containers.Mini.rawsys_not_sound`), because a run with undefined
  behaviour satisfies every partial-correctness specification taken alone;
* `checkSys check φ`: the judgements a decidable checker on images makes: `i ⊢ φ` when
  `check i = true`. It is sound for `vsys R` exactly when the checker is a verified sufficient
  precondition (`Thms.checkSys_sound_iff`), that is, `Accept.Sound` for the images satisfying
  `vpre R φ`.

The laws a system for container obligations must satisfy are proved of `vsys` in
`Thms`: every judgement excludes undefined behaviour (`vsys_noUB`); weakening of the conclusion and
conjunction (`vsys_mono`, `vsys_and`); antitonicity in the runtime model
(`vsys_sound_of_le`: a model with fewer runs proves more); assumptions do not mask undefined
behaviour (`vsys_restrict_noUB`); and soundness for raw satisfaction (`vsys_sound_raw`).

**Acceptors** (`Silmaril.Acceptor`). A run is observed as a stream (`Obs`): its events, then its
stop if it has one, so **undefined behaviour is an observation**. `vmonitor ok` is an online
acceptor over chunks of observations: it answers whether everything observed so far is an allowed
event or a stop other than undefined behaviour. It is correct for the language `vlang ok` in the
interleaved protocol (`Thms.vmonitor_correctInterleaved`), and a run has no undefined behaviour and
only allowed events exactly when every observation prefix of it is in `vlang ok`
(`Thms.vlang_iff`). So an acceptor's answer is a verified, no-undefined-behaviour judgement about a
run, never raw trace satisfaction.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers.Check

open Silmaril.Containers Silmaril.Consequence

variable {I P E : Type}

/-! ## Consequence systems -/

/-- **The verified system**: `i ⊢ φ` iff no run of `i` under `R` has undefined behaviour, and every
run satisfies `φ`. -/
def vsys (R : Runtime I P E) : System I (Spec E) := fun i φ => vpre R φ i

/-- **The raw system**: `i ⊢ φ` iff every run of `i` under `R` satisfies `φ`. A comparison only. -/
def rawsys (R : Runtime I P E) : System I (Spec E) := fun i φ => pre R φ i

/-- **The system of a checker**: a decidable checker on images judges `i ⊢ φ` when it accepts `i`. -/
def checkSys (check : I → Bool) (φ : Spec E) : System I (Spec E) :=
  fun i ψ => check i = true ∧ ψ = φ

/-- The images a checker should accept for `φ`: those satisfying the verification precondition. -/
def vset (R : Runtime I P E) (φ : Spec E) : Set I := {i | vpre R φ i}

/-! ## Observations and the monitor -/

/-- Whether a stop is undefined behaviour. -/
def _root_.Silmaril.Containers.Stop.isUB : Stop → Bool
  | .undefined _ => true
  | _ => false

/-- **An observation** of a run: an event, or how it stopped. -/
inductive Obs (E : Type) where
  | ev (e : E)
  | stop (s : Stop)

/-- An observation is allowed: an allowed event, or a stop other than undefined behaviour. -/
def Obs.ok {E : Type} (ok : E → Bool) : Obs E → Bool
  | .ev e => ok e
  | .stop s => !s.isUB

/-- **The observation prefixes of a run**: the prefixes of its events, and, for a stopped run, its
events followed by its stop. -/
def ObsPrefix {E : Type} (b : Beh E) (w : List (Obs E)) : Prop :=
  (∃ t, b.Prefix t ∧ w = t.map .ev) ∨ ∃ t s, b = .done t s ∧ w = t.map .ev ++ [.stop s]

/-- **The language of the monitor**: observation sequences that are all allowed. -/
def vlang {E : Type} (ok : E → Bool) : Language (Obs E) := {w | w.all (Obs.ok ok) = true}

instance {E : Type} (ok : E → Bool) : DecidablePred (· ∈ vlang ok) :=
  fun w => inferInstanceAs (Decidable (w.all (Obs.ok ok) = true))

/-- **The monitor**: whether every observation so far is allowed (an online acceptor over chunks
of observations). -/
def vmonitor {E : Type} (ok : E → Bool) : Silmaril.Acceptor Bool (List (Obs E)) where
  init := true
  process b c := b && c.all (Obs.ok ok)
  query b := (b, b)
  reset _ := true

end Silmaril.Containers.Check
