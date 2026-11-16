module

public import Silmaril.Wasi.Component.Consequence.Stateful.Defs
public import Silmaril.Wasi.Component.Consequence.Thms
import Silmaril.Proofs.Wasi.Component.Consequence.Stateful

/-! # A stateful specification checker: theorems

About the **specification strategy** `statefulMember enc` (not a compiled component), through
protocol 2 with assumptions and resets observed at their calls and the `list` policy
(`exportStateful .call statefulFns Policy.list decA decC`), for decoders that invert the
encoding:

* every completed `check` answers membership in the current epoch's assumptions
  (`answered_statefulMember`);
* it accepts `(xs, c)` exactly when `c ∈ xs` (`accepted_statefulMember`);
* its execution status is `STH` when `c ∈ xs` and `SCT` otherwise (`status_statefulMember`);
* concretely, at `u32` (`accepted_statefulMemberU32`).

Proofs: `Silmaril.Proofs.Wasi.Component.Consequence.Stateful`.
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence

open Silmaril.Wasi.Accept (Traces)
open Silmaril.Wasm.Component (Val)

variable {C : Type} [DecidableEq C] {enc : C → Val} {decA decC : List Val → Option C}

/-- **The answers of the stateful checker**: membership in the current epoch. -/
theorem answered_statefulMember (hA : ∀ args a, decA args = some a ↔ args = [enc a])
    (hC : ∀ args c, decC args = some c ↔ args = [enc c]) (xs : List C) (c : C) (a : Answer) :
    Answered (Traces (statefulMember enc))
      (exportStateful .call statefulFns Policy.list decA decC) xs c a ↔
      a = .ofResult (some [.bool (decide (c ∈ xs))]) :=
  Proofs.Wasi.Component.Consequence.answered_statefulMember hA hC xs c a

/-- **The stateful checker accepts exactly the membership rule on the current epoch.** -/
theorem accepted_statefulMember (hA : ∀ args a, decA args = some a ↔ args = [enc a])
    (hC : ∀ args c, decC args = some c ↔ args = [enc c]) (xs : List C) (c : C) :
    Accepted (Traces (statefulMember enc))
      (exportStateful .call statefulFns Policy.list decA decC) xs c ↔ c ∈ xs :=
  (answered_statefulMember hA hC xs c .yes).trans (by by_cases h : c ∈ xs <;> simp [h])

theorem status_statefulMember (hA : ∀ args a, decA args = some a ↔ args = [enc a])
    (hC : ∀ args c, decC args = some c ↔ args = [enc c]) (xs : List C) (c : C) :
    (status (Traces (statefulMember enc))
      (exportStateful .call statefulFns Policy.list decA decC) xs c).exec =
      if c ∈ xs then .STH else .SCT := by
  rw [status, Proofs.Wasi.Component.Consequence.classify_of_answered_iff
    (answered_statefulMember hA hC xs c)]
  by_cases h : c ∈ xs <;> simp [h]

theorem u32Arg_iff (args : List Val) (c : BitVec 32) : u32Arg args = some c ↔ args = [.u32 c] :=
  Proofs.Wasi.Component.Consequence.u32Arg_iff args c

/-- **Concretely, at `u32`.** -/
theorem accepted_statefulMemberU32 (xs : List (BitVec 32)) (c : BitVec 32) :
    Accepted (Traces statefulMemberU32)
      (exportStateful .call statefulFns Policy.list u32Arg u32Arg) xs c ↔ c ∈ xs :=
  accepted_statefulMember u32Arg_iff u32Arg_iff xs c

end Silmaril.Wasi.Consequence
