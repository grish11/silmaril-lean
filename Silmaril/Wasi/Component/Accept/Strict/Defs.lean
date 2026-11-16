module

public import Silmaril.Wasi.Component.Accept.Reject.Defs
public import Silmaril.Semantics.Accept.Verdict.Defs

/-! # Components: some play accepts and no play rejects

The combined reading of an accepting and a rejecting function, in both modes, uses **one**
runner for both quantifiers: the events of the plays of the same strategy (so the same hosts
and callers):

* exported (`exportAcceptedNotRejected σ acc rej dec`, `Reject`): some call of `acc` with the
  value returns `true`, and no call of `rej` with it returns `false`;
* imported (`importAcceptedNotRejected σ acc rej dec`): the component calls `acc` with the
  value in some play and calls `rej` with it in none.

`exportRun σ dec` and `importRun σ dec` are the runners. They send a value to the return
events, resp. import requests, carrying it in some play. `retWith f b` and `reqOf f` are the
accepting and rejecting outcomes. `Thms` identifies both combined sets with
`Silmaril.Accept.acceptsSafely` (#296).

**Specification components for the cases** (`verdictComponent A R`): on a call of `accept(w)`
it may return `true` when `w ∈ A`; on a call of `reject(w)` it may return `false` when
`w ∈ R`. It answers nothing else, and a call may stay unanswered (receptiveness: the
environment may call any export at any time). Its combined language is `A \ R`
(`Silmaril.Wasi.Accept.Examples`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games Silmaril.Formats.Accept
open Silmaril.Wasm.Component (Val)

variable {I X : Set FnName} {α : Type}

/-- The value of a return event, decoded from its call's arguments. -/
def retValue (dec : List Val → Option α) : WEv → Option α
  | .ret _ args _ => dec args
  | _ => none

/-- The value of an import request, decoded from its arguments. -/
def reqValue (dec : List Val → Option α) : WEv → Option α
  | .req _ args => dec args
  | _ => none

/-- Return events of the export `f` with result `bool b`. -/
def retWith (f : FnName) (b : Bool) : Set WEv := {e | ∃ args, e = .ret f args (some [.bool b])}

/-- Requests of the import `f`. -/
def reqOf (f : FnName) : Set WEv := {e | ∃ args, e = .req f args}

/-- **The export runner**: the return events carrying a value, over all plays. -/
def exportRun (σ : Strategy (nsig I) (nsig X)) (dec : List Val → Option α) (a : α) : Set WEv :=
  {e | (∃ t ∈ Traces σ, e ∈ t) ∧ retValue dec e = some a}

/-- **The import runner**: the import requests carrying a value, over all plays. -/
def importRun (σ : Strategy (nsig I) (nsig X)) (dec : List Val → Option α) (a : α) : Set WEv :=
  {e | (∃ t ∈ Traces σ, e ∈ t) ∧ reqValue dec e = some a}

/-- Called through the import `acc` in some play, through the import `rej` in none. -/
def importAcceptedNotRejected (σ : Strategy (nsig I) (nsig X)) (acc rej : FnName)
    (dec : List Val → Option α) : Lang α :=
  importAccepted σ acc dec ∩ neverCalled σ rej dec

/-! ## Specification components for the cases -/

/-- The world of the examples: exports `accept` and `reject`. -/
def verdictFns : Set FnName := {acceptFn, ⟨"", "reject"⟩}

/-- The export `reject` of the examples. -/
def rejectExport : FnName := ⟨"", "reject"⟩

theorem acceptFn_mem_verdictFns : acceptFn ∈ verdictFns := Set.mem_insert _ _

theorem rejectExport_mem_verdictFns : rejectExport ∈ verdictFns :=
  Set.mem_insert_of_mem _ rfl

/-- The generating plays: `accept(w)` returns `true` for `w ∈ A`; `reject(w)` returns `false`
for `w ∈ R`. -/
def verdictPlays (A R : ByteLang) : Set (List (Move (nsig ∅) (nsig verdictFns))) :=
  {s | ∃ w ∈ A, s = [.inr (.ask (⟨acceptFn, acceptFn_mem_verdictFns⟩, [bytesVal w])),
      .inr (.ans (⟨acceptFn, acceptFn_mem_verdictFns⟩, [bytesVal w]) (some [.bool true]))]} ∪
  {s | ∃ w ∈ R, s = [.inr (.ask (⟨rejectExport, rejectExport_mem_verdictFns⟩, [bytesVal w])),
      .inr (.ans (⟨rejectExport, rejectExport_mem_verdictFns⟩, [bytesVal w])
        (some [.bool false]))]}

/-- **The component accepting `A` and rejecting `R`**, on different calls. -/
def verdictComponent (A R : ByteLang) : Strategy (nsig ∅) (nsig verdictFns) :=
  Strategy.generate (verdictPlays A R)

end Silmaril.Wasi.Accept
