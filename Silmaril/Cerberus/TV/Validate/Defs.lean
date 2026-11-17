module

public import Silmaril.Cerberus.TV.Explore.Defs

/-!
# A whole-program refinement validator for closed Core programs

`validate impl src tgt bounds` decides `Refines impl src tgt` (`TV.Behaviour`) for programs whose
executions are finite and fit the bounds, and says `unknown` otherwise. It explores both programs
(`Closed.explore`) and checks that every ending of the target is **covered** by an ending of the
source: each observation the target ending admits, the source ending admits too (`covers`).

| verdict | meaning | theorem (`Thms`) |
|---|---|---|
| `validated` | the target exploration was exhaustive, found no gap and no stuck state, and every target ending is covered | `validate_sound`: `Refines impl src tgt` |
| `refuted` | both explorations were exhaustive, the source stayed in the supported fragment, and some target ending admits an observation (`witness`) that no source ending admits | `validate_refuted`: `¬ Refines impl src tgt` |
| `unsupported` | the target exploration reached a gap (`error`, `unsupported`) or a stuck state | none: the target leaves the fragment the Lean dynamics defines |
| `unknown` | a bound was hit, or an uncovered target ending has no witness the check can use | none |

A covered target ending may be covered **only** by source endings that are undefined behaviour
(UB admits every observation). The verdict is still `validated`, and the report's
`coveredOnlyByUB` says so: the target is then unconstrained on that execution, which is C's
meaning, but rarely what a reader of "validated" expects.

The source exploration need not be exhaustive for `validated`: its endings are sound whatever the
bounds, so covering by them is sound. Source gaps make `validated` only more conservative (a gap
covers nothing) and block `refuted`.
-/

@[expose] public section

namespace Silmaril.Cerberus.TV

open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Spec

/-- **Coverage of one ending by another** (`s` covers `e`): every observation `e` admits, `s`
admits (`covers_sound` in `Thms`). Undefined behaviour covers everything; equal stdout with the
same exit status (or an unspecified exit value on the source side) covers an exit; an abort covers
an abort with the same stdout. Nothing else covers. -/
def covers (impl : Impl) (s e : Outcome × String) : Bool :=
  match s.1, e.1 with
  | .ub _ _, _ => true
  | .defined v', .defined v =>
      decide (s.2 = e.2) && match exitValue v', exitValue v with
        | .int m, .int n => decide (impl.status m = impl.status n)
        | .unspecified, .int _ => true
        | .unspecified, .unspecified => true
        | _, _ => false
  | .aborted, .aborted => decide (s.2 = e.2)
  | _, _ => false

/-- An observation an ending admits (`witness_admits`), when one is readily named. For undefined
behaviour it is termination by signal 0 with no output, which only undefined behaviour admits. -/
def witness (impl : Impl) (e : Outcome × String) : Option Obs :=
  match e.1 with
  | .defined v => match exitValue v with
    | .int n => some ⟨.exit (impl.status n), bytes e.2⟩
    | .unspecified => some ⟨.exit 0, bytes e.2⟩
    | .other => none
  | .aborted => some ⟨.abort, bytes e.2⟩
  | .ub _ _ => some ⟨.signal 0, []⟩
  | _ => none

/-- No source ending admits the target ending's witness. -/
def refutes (impl : Impl) (source : List (Outcome × String)) (e : Outcome × String) : Bool :=
  match witness impl e with
  | some x => source.all fun s => !decide (admits impl s.1 s.2 x)
  | none => false

inductive Verdict where
  | validated
  | refuted
  | unsupported
  | unknown
  deriving DecidableEq, Repr

/-- The validator's report. -/
structure Report where
  verdict : Verdict
  /-- The source exploration. -/
  source : Leaves
  /-- The target exploration. -/
  target : Leaves
  /-- Target endings no source ending covers. -/
  uncovered : List (Outcome × String)
  /-- Some target ending is covered only by source endings that are undefined behaviour. -/
  coveredOnlyByUB : Bool

/-- Whether some source ending covers `e`. -/
def covered (impl : Impl) (source : List (Outcome × String)) (e : Outcome × String) : Bool :=
  source.any fun s => covers impl s e

/-- **The validator.** -/
def validate (impl : Impl) (src tgt : Closed) (bounds : Bounds := {}) : Report :=
  let S := src.explore bounds
  let T := tgt.explore bounds
  let uncovered := T.ends.filter fun e => !covered impl S.ends e
  let onlyUB := T.ends.any fun e =>
    covered impl S.ends e && !covered impl (S.ends.filter fun s => !Outcome.isUB s.1) e
  let verdict :=
    if T.limited then .unknown
    else if T.stuck || T.gap then .unsupported
    else if uncovered.isEmpty then .validated
    else if !S.limited && !S.stuck && !S.gap && uncovered.any (refutes impl S.ends) then .refuted
    else .unknown
  { verdict, source := S, target := T, uncovered, coveredOnlyByUB := onlyUB }

/-- **The equivalence validator**: `validated` both ways. -/
def validateEquivalent (impl : Impl) (P Q : Closed) (bounds : Bounds := {}) : Bool :=
  (validate impl P Q bounds).verdict == .validated && (validate impl Q P bounds).verdict == .validated

end Silmaril.Cerberus.TV
