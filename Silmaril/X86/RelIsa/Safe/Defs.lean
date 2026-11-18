module

public import Silmaril.X86.RelIsa.Defs
public import Silmaril.X86.Sep.Defs

/-!
# Demonic step-indexed safety and triples over a relational machine (`SafeNR`)

* `ofFun step`: a step *function* on `MState` as a relational machine (`none` ↦ `stop`), over
  the `MState` views. `ofIsa Open.isa = ofFun Open.step` (`RelIsa/Safe/Thms.lean`).
* `SafeNR A Q n m`: **demonic step-indexed partial correctness.** Within `n` steps from `m`,
  either `Q` holds, or *every* outcome of `A` at `m` is a successor (never `stop`) from which
  `SafeNR A Q (n - 1)` holds. On `ofFun step` it is `Safe.SafeN step` (`safeNR_ofFun`).
  As with `Must`, a state with no outcome at all is vacuously safe: a consumer that reads a
  run out of `SafeNR` needs progress of its machine (for `ofFun` that is automatic, see
  `safeN_of_safeNR`).
* `STripleR A n P Q`: the frame-quantified step-indexed triple on `A` (`Safe.STriple` with
  `SafeNR A` for `SafeN step`).
* `TripleR A P Q`: the frame-quantified **total** demonic triple: `Must A ⊤ (Q ∗ F)` from every
  `P ∗ F` state (`Sep.Triple` with `Must` for `∃ Reaches`).

Only the definitions are here; the glibc bridge of the Wasm simulators
(`Silmaril.Sim.GlibcBridge.Link`) uses them.
-/

@[expose] public section

namespace Silmaril.X86.RelIsa

open Silmaril.X86 (MState)
open Silmaril.X86.Sep

/-- A step function on `MState` as a relational machine: `none` becomes an explicit `stop`. -/
def ofFun (step : MState → Option MState) : RelIsa MState where
  toViews := Views.mstate
  step s r := match step s with
    | some t => r = .ok t
    | none => r = .stop
  live_step _ _ := trivial

/-- **Demonic step-indexed partial correctness** on the relational machine `A`. -/
def SafeNR {σ : Type} (A : RelIsa σ) (Q : σ → Prop) : Nat → σ → Prop
  | 0, _ => True
  | n + 1, m => Q m ∨ ∀ r, A.step m r → ∃ m', r = .ok m' ∧ SafeNR A Q n m'

/-- **A demonic step-indexed triple** on `A`, frame built in. -/
def STripleR (A : RelIsa MState) (n : Nat) (P Q : SProp) : Prop :=
  ∀ (F : SProp) (m : MState), (P ∗ F) (toFrag m) →
    SafeNR A (fun m' => (Q ∗ F) (toFrag m')) n m

/-- **A demonic total triple** on `A`, frame built in: every run from a `P ∗ F` state
terminates in a `Q ∗ F` state without stopping. -/
def TripleR (A : RelIsa MState) (P Q : SProp) : Prop :=
  ∀ (F : SProp) (m : MState), (P ∗ F) (toFrag m) →
    Must A (fun _ => True) (fun m' => (Q ∗ F) (toFrag m')) m

end Silmaril.X86.RelIsa
