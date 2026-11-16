module

public import Silmaril.Wasi.Component.Accept.Session.Defs
public import Silmaril.Wasi.Component.Accept.Stream.Thms
public import Silmaril.Wasi.World.Exports.Thms
import Silmaril.Proofs.Wasi.Component.Accept.Session

/-! # Incremental components as client sessions: theorems

The bridge from `StreamCorrect` (`Silmaril.Wasi.Component.Accept.Stream`) to the session
relations of `Silmaril.Semantics.Accept.Session` (#278). It holds for every component, under the
actual game rules: legal plays, with their export calls and returns alternating and matched
(`Silmaril.Wasi.exportAlt_of_legal`). Import calls and host answers may occur between a call
and its return; they are not session events.

* **`freshFeedsQuery_sound`**: in a fresh session (no earlier call), if the chunks `as` are fed
  and a `query()` returns `bool b`, then `b = decide (as.flatten ∈ L)`. No hypothesis beyond
  distinct function names.
* **`feedsQuery_sound`**: the same after any `reset` (`Silmaril.Accept.feedsQuery`), if every
  completed `query()` of the component returns a `bool` (`QueryTotal`). The hypothesis is needed:
  `StreamCorrect` aligns the `bool` answers with the query *calls*, so an earlier query that traps
  or returns a non-`bool` shifts that alignment.
* `freshFeedsQuery_subset`, `feedsQuery_subset`: the same as inclusions of the session relation
  in the graph of membership (answers `none`, traps or non-`bool`s, are unconstrained).

The proofs are in `Silmaril.Proofs.Wasi.Component.Accept.Session`, by induction on the matched
export events.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games Silmaril.Formats.Accept

variable {I X : Set FnName} {fns : StreamFns} {σ : Strategy (nsig I) (nsig X)} {L : ByteLang}
  [DecidablePred (· ∈ L)]

/-- **A fresh session's answer is membership of the chunks fed.** -/
theorem freshFeedsQuery_sound (hd : fns.Distinct) (hc : StreamCorrect fns σ L)
    {as : List (List UInt8)} {b : Bool}
    (h : (as, some b) ∈ Silmaril.Accept.freshFeedsQuery (sessionTraces fns σ)) :
    b = decide (as.flatten ∈ L) :=
  Silmaril.Proofs.Wasi.Component.Accept.freshFeedsQuery_sound hd hc h

/-- **A session's answer after a reset is membership of the chunks fed since**, when every
completed query returns a `bool`. -/
theorem feedsQuery_sound (hd : fns.Distinct) (hc : StreamCorrect fns σ L)
    (ht : QueryTotal fns σ) {as : List (List UInt8)} {b : Bool}
    (h : (as, some b) ∈ Silmaril.Accept.feedsQuery (sessionTraces fns σ)) :
    b = decide (as.flatten ∈ L) :=
  Silmaril.Proofs.Wasi.Component.Accept.feedsQuery_sound hd hc ht h

/-- The fresh session relation lies in the graph of membership (or answers `none`). -/
theorem freshFeedsQuery_subset (hd : fns.Distinct) (hc : StreamCorrect fns σ L) :
    Silmaril.Accept.freshFeedsQuery (sessionTraces fns σ) ⊆
      {p | p.2 = none ∨ p.2 = some (decide (p.1.flatten ∈ L))} := by
  rintro ⟨as, _ | b⟩ h
  · exact .inl rfl
  · exact .inr (congrArg some (freshFeedsQuery_sound hd hc h))

/-- The session relation lies in the graph of membership, when queries are total. -/
theorem feedsQuery_subset (hd : fns.Distinct) (hc : StreamCorrect fns σ L)
    (ht : QueryTotal fns σ) :
    Silmaril.Accept.feedsQuery (sessionTraces fns σ) ⊆
      {p | p.2 = none ∨ p.2 = some (decide (p.1.flatten ∈ L))} := by
  rintro ⟨as, _ | b⟩ h
  · exact .inl rfl
  · exact .inr (congrArg some (feedsQuery_sound hd hc ht h))

/-- Refinement keeps the bridge: a strategy refining a correct one has a sound session relation. -/
theorem freshFeedsQuery_sound_of_le (hd : fns.Distinct) {τ : Strategy (nsig I) (nsig X)}
    (hc : StreamCorrect fns τ L) (hle : σ ≤ τ) {as : List (List UInt8)} {b : Bool}
    (h : (as, some b) ∈ Silmaril.Accept.freshFeedsQuery (sessionTraces fns σ)) :
    b = decide (as.flatten ∈ L) :=
  freshFeedsQuery_sound hd (hc.of_le hle) h

end Silmaril.Wasi.Accept
