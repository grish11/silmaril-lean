module

public import Silmaril.Wasi.Component.Consequence.Checkers.Defs
public import Silmaril.Wasi.Component.Consequence.Thms
import Silmaril.Proofs.Wasi.Component.Consequence.Checkers

/-! # Specification checker components: theorems

All about the **specification strategies** of `Silmaril.Wasi.Component.Consequence.Checkers.Defs`,
through protocol 1 (`exportCheck checkFn dec`), for a decoder `dec` that inverts the encoding
(`dec args = some q ↔ args = enc q`; `u32Dec_iff` for the concrete `list<u32>`/`u32` encoding).

* `answerChecker enc ans`: every completed query is answered `ans q`
  (`answered_answerChecker`); accepted iff `ans q` (`accepted_answerChecker`); execution status
  `STH` or `SCT` (`status_answerChecker`), never `CAX` or `NOC`.
* **Two empty relations, two statuses**: the empty checker accepts nothing and every query
  completes `false`, so its status is `SCT` (`status_emptyChecker`); the silent checker accepts
  nothing because nothing completes, so its status is `CAX` and `THM` holds vacuously
  (`status_silentChecker`, `thm_silentChecker`).
* **The membership rule, exactly**: the membership checker accepts `(xs, c)` iff `c ∈ xs`
  (`accepted_memberChecker`), sound and complete for the membership relation
  (`memberChecker_sound`, `memberChecker_complete`); concretely `accepted_memberU32`.

Proofs: `Silmaril.Proofs.Wasi.Component.Consequence.Checkers`.
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence

open Silmaril.Logic.Szs
open Silmaril.Wasi.Accept (Traces)
open Silmaril.Wasm.Component (Val)

variable {X C : Type} {dec : List Val → Option (X × C)}

/-- **The checker answers exactly `ans (x, c)`.** -/
theorem answered_answerChecker {enc : X × C → List Val} {ans : X × C → Bool}
    (hdec : ∀ args q, dec args = some q ↔ args = enc q) (x : X) (c : C) (a : Answer) :
    Answered (Traces (answerChecker enc ans)) (exportCheck checkFn dec) x c a ↔
      a = .ofResult (some [.bool (ans (x, c))]) :=
  Proofs.Wasi.Component.Consequence.answered_answerChecker hdec x c a

theorem accepted_answerChecker {enc : X × C → List Val} {ans : X × C → Bool}
    (hdec : ∀ args q, dec args = some q ↔ args = enc q) (x : X) (c : C) :
    Accepted (Traces (answerChecker enc ans)) (exportCheck checkFn dec) x c ↔ ans (x, c) :=
  (answered_answerChecker hdec x c .yes).trans (by cases ans (x, c) <;> simp [Answer.ofResult])

/-- **The execution status of the checker**: `STH` when it answers `true`, `SCT` otherwise. -/
theorem status_answerChecker {enc : X × C → List Val} {ans : X × C → Bool}
    (hdec : ∀ args q, dec args = some q ↔ args = enc q) (x : X) (c : C) :
    (status (Traces (answerChecker enc ans)) (exportCheck checkFn dec) x c).exec =
      if ans (x, c) then .STH else .SCT := by
  rw [status, Proofs.Wasi.Component.Consequence.classify_of_answered_iff
    (answered_answerChecker hdec x c)]
  cases ans (x, c) <;> rfl

/-- The empty checker accepts nothing. -/
theorem not_accepted_emptyChecker {enc : X × C → List Val}
    (hdec : ∀ args q, dec args = some q ↔ args = enc q) (x : X) (c : C) :
    ¬ Accepted (Traces (emptyChecker enc)) (exportCheck checkFn dec) x c :=
  fun h => Bool.false_ne_true ((accepted_answerChecker hdec x c).1 h)

/-- **The empty checker's status is `SCT`**: every query completes, answered `false`. -/
theorem status_emptyChecker {enc : X × C → List Val}
    (hdec : ∀ args q, dec args = some q ↔ args = enc q) (x : X) (c : C) :
    (status (Traces (emptyChecker enc)) (exportCheck checkFn dec) x c).exec = .SCT :=
  status_answerChecker hdec x c

/-- No query of the silent checker completes. -/
theorem not_answered_silentChecker (x : X) (c : C) (a : Answer) :
    ¬ Answered (Traces silentChecker) (exportCheck checkFn dec) x c a :=
  Proofs.Wasi.Component.Consequence.not_answered_silentChecker x c a

theorem not_accepted_silentChecker (x : X) (c : C) :
    ¬ Accepted (Traces silentChecker) (exportCheck checkFn dec) x c :=
  not_answered_silentChecker x c .yes

/-- **The silent checker's status is `CAX`.** -/
theorem status_silentChecker (x : X) (c : C) :
    (status (Traces silentChecker) (exportCheck checkFn dec) x c).exec = .CAX :=
  (classify_eq_cax_iff _).2 (execProblem_cax_iff.2 (not_answered_silentChecker x c))

/-- **…and its `THM` holds vacuously**, without acceptance. -/
theorem thm_silentChecker (x : X) (c : C) :
    Current.THM (execProblem (Traces silentChecker) (exportCheck checkFn dec) x c) :=
  thm_of_cax (execProblem_cax_iff.2 (not_answered_silentChecker x c))

variable {D : Type} [DecidableEq D] {encL : List D → Val} {encC : D → Val}
  {decM : List Val → Option (List D × D)}

/-- **The membership checker accepts exactly the membership rule.** -/
theorem accepted_memberChecker
    (hdec : ∀ args q, decM args = some q ↔ args = [encL q.1, encC q.2])
    (xs : List D) (c : D) :
    Accepted (Traces (memberChecker encL encC)) (exportCheck checkFn decM) xs c ↔ c ∈ xs :=
  (accepted_answerChecker hdec xs c).trans (by simp)

theorem memberChecker_sound
    (hdec : ∀ args q, decM args = some q ↔ args = [encL q.1, encC q.2]) :
    Sound (Accepted (Traces (memberChecker encL encC)) (exportCheck checkFn decM))
      fun xs c => c ∈ xs :=
  fun xs c => (accepted_memberChecker hdec xs c).1

theorem memberChecker_complete
    (hdec : ∀ args q, decM args = some q ↔ args = [encL q.1, encC q.2]) :
    Complete (Accepted (Traces (memberChecker encL encC)) (exportCheck checkFn decM))
      fun xs c => c ∈ xs :=
  fun xs c => (accepted_memberChecker hdec xs c).2

/-- The `list<u32>`/`u32` decoder inverts the encoding. -/
theorem u32Dec_iff (args : List Val) (q : List (BitVec 32) × BitVec 32) :
    u32Dec args = some q ↔ args = u32Enc q :=
  Proofs.Wasi.Component.Consequence.u32Dec_iff args q

/-- **Concretely**: the `list<u32>`/`u32` membership checker accepts `(xs, c)` iff `c ∈ xs`. -/
theorem accepted_memberU32 (xs : List (BitVec 32)) (c : BitVec 32) :
    Accepted (Traces memberU32) (exportCheck checkFn u32Dec) xs c ↔ c ∈ xs :=
  accepted_memberChecker u32Dec_iff xs c

theorem status_memberU32 (xs : List (BitVec 32)) (c : BitVec 32) :
    (status (Traces memberU32) (exportCheck checkFn u32Dec) xs c).exec =
      if c ∈ xs then .STH else .SCT := by
  have := status_answerChecker (enc := u32Enc) (ans := fun q => decide (q.2 ∈ q.1))
    u32Dec_iff xs c
  simp only [decide_eq_true_eq] at this
  exact this

theorem status_emptyU32 (xs : List (BitVec 32)) (c : BitVec 32) :
    (status (Traces emptyU32) (exportCheck checkFn u32Dec) xs c).exec = .SCT :=
  status_emptyChecker u32Dec_iff xs c

end Silmaril.Wasi.Consequence
