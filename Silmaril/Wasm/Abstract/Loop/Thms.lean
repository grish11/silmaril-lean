module

public import Silmaril.Wasm.Abstract.Loop.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Wasm.Abstract.Body.Thms
import Silmaril.Proofs.Wasm.Abstract.Loop.Basic

/-!
# Abstract Wasm loops: theorems

**The bridge for loops.**

* `toAFun_loop`: the trace denotation of a loop is the trace-set iteration of
  the denotation of its body, `AFun.iter`. Exact, with no determinism or
  productivity assumption.
* `collapse_loop`: the trap ≈ divergence collapse of a loop is the loop of the
  collapsed body (in `BodyC`).
* `toAFun_loop_obsCollapse`: loops whose bodies have trap ≈ divergence
  equivalent denotations have trap ≈ divergence equivalent denotations.

**Divergence, accounted for.**

* `toAFun_spin`: `loop br 0 end` denotes exactly `([], div)`. No iteration
  diverges; the infinite chain of silent iterations does.
* `toAFun_trapLoop`: `loop unreachable end` denotes exactly `([], trap)`.
* `toAFun_pollLoop`: `loop call m; br 0 end` denotes **no** behaviour: its only
  run is infinite and productive, and the trace sets keep finite behaviours
  only.
* `spin_ne_trapLoop`, `spin_obsCollapse_trapLoop`, `collapse_trapLoop`: the
  sensitive observation separates the silent loop from the trapping one; the
  trap ≈ divergence observation identifies them, both at the trace level and
  as collapsed bodies.

**The denotation is not faithful.** `toAFun_not_injective`: two bodies that
trap with different payloads are different bodies with the same denotation.
Infinite productive runs are forgotten too (`toAFun_pollLoop`: every
productive loop denotes the empty set). So `toAFun` is a structure-preserving
map of composition (`toAFun_comp`) and iteration (`toAFun_loop`), not an
embedding.
-/

public section

namespace Silmaril.Wasm.Abstract.Loop

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace

universe u

variable {E : Sig.{u}} {S T A B : Type (u + 1)}

/-- The denotation of a loop is the iteration of the denotation of its body. -/
theorem toAFun_loop (F : Hom E S T A (B ⊕ A)) : toAFun (loop F) = AFun.iter (toAFun F) :=
  toAFun_iter F

/-- Collapsing a loop collapses its body. -/
theorem collapse_loop (F : Hom E S T A (B ⊕ A)) (a : A) :
    collapse (loop F a) = Silmaril.Elgot.iter (fun a => collapse (F a)) a :=
  collapse_iter F a

/-- Trap ≈ divergence equivalent loop bodies give equivalent loops. -/
theorem toAFun_loop_obsCollapse {F G : Hom E S T A (B ⊕ A)}
    (h : AFun.ObsEquiv AFun.obsCollapse (toAFun F) (toAFun G)) :
    AFun.ObsEquiv AFun.obsCollapse (toAFun (loop F)) (toAFun (loop G)) :=
  toAFun_iter_obsCollapse h

/-- The silent loop diverges silently. -/
theorem toAFun_spin (s : S) (a : A) : toAFun (spin : Hom E S T A B) s a = {([], .div)} :=
  Silmaril.Proofs.Wasm.Abstract.Loop.toAFun_spin s a

/-- The trapping loop traps. -/
theorem toAFun_trapLoop (t : T) (s : S) (a : A) :
    toAFun (trapLoop t : Hom E S T A B) s a = {([], .trap)} :=
  Silmaril.Proofs.Wasm.Abstract.Loop.toAFun_trapLoop t s a

/-- The productive loop has no finite behaviour. -/
theorem toAFun_pollLoop (m : E.Op) (s : S) (a : A) :
    toAFun (pollLoop m : Hom E S T A B) s a = ∅ :=
  Silmaril.Proofs.Wasm.Abstract.Loop.toAFun_pollLoop m s a

/-- The sensitive denotation separates the silent and the trapping loop. -/
theorem spin_ne_trapLoop (t : T) (s : S) (a : A) :
    toAFun (spin : Hom E S T A B) s a ≠ toAFun (trapLoop t) s a := by
  rw [toAFun_spin, toAFun_trapLoop]; simp

/-- As collapsed bodies, the trapping loop and the silent loop are equal. -/
theorem collapse_trapLoop (t : T) (a : A) :
    collapse (trapLoop t a : BodyM E S T B) = collapse (spin a : BodyM E S T B) :=
  Silmaril.Proofs.Wasm.Abstract.Loop.collapse_trapLoop t a

/-- Trap ≈ divergence identifies their denotations. -/
theorem spin_obsCollapse_trapLoop (t : T) :
    AFun.ObsEquiv AFun.obsCollapse (toAFun (spin : Hom E S T A B)) (toAFun (trapLoop t)) :=
  obsCollapse_of_collapse fun a => (collapse_trapLoop t a).symm

/-- The silent loop and the productive loop have different denotations. -/
theorem spin_ne_pollLoop (m : E.Op) (s : S) (a : A) :
    toAFun (spin : Hom E S T A B) s a ≠ toAFun (pollLoop m : Hom E S T A B) s a := by
  rw [toAFun_spin, toAFun_pollLoop]; simp

/-- The denotation is not injective: trap payloads are forgotten. -/
theorem toAFun_not_injective :
    ∃ f g : Hom Sig.empty.{0} PUnit.{2} (ULift.{1} Bool) PUnit.{2} PUnit.{2},
      f ≠ g ∧ toAFun f = toAFun g :=
  ⟨_, _, Silmaril.Proofs.Wasm.Abstract.Loop.toAFun_not_injective⟩

end Silmaril.Wasm.Abstract.Loop
