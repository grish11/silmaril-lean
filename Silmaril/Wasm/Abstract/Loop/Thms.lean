module

public import Silmaril.Wasm.Abstract.Loop.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Wasm.Abstract.Body.Thms
public import Silmaril.Games.Abstract.Module.Thms
import Silmaril.Proofs.Wasm.Abstract.Loop.Basic

/-!
# Abstract Wasm loops: theorems

All statements are about abstract body loops and their finite trace-and-outcome
denotation `toAFun`, not about Core Wasm execution.

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

**Productive runs are forgotten, even up to trap ≈ divergence.** For distinct
imports `m₁ ≠ m₂`, `pollLoop m₁` and `pollLoop m₂` run different forever-import
streams (`m₁ m₁ …` against `m₂ m₂ …`): they are different bodies, and even their
collapses differ (`collapse_pollLoop_ne`), yet both denote `∅`
(`toAFun_pollLoop_eq`). So the converse of `obsCollapse_of_collapse` is false
(`obsCollapse_not_collapse`, `exists_obsCollapse_not_collapse`): equality of
the finite trace-and-outcome denotation, even sensitive, does not determine
the body, nor its trap ≈ divergence collapse. `toAFun_iter` is exact *relative
to finite observations*; it is not a behavioural equivalence of bodies, and
`toAFun` is not a faithful functor on any quotient that keeps import streams.

**Pending calls see them.** `mem_toPending_pollLoop`: the first pending call
of `pollLoop m` is `m`. With pending calls the observation is faithful up to
collapse (`BodyTrace.fullCollapseEquiv_iff`): `pollLoop_not_fullCollapseEquiv`
separates the two forever-import loops, while `spin_fullCollapseEquiv_trapLoop`
still identifies the silent and the trapping loop.

**Infinite streams.** `toInf_pollLoop`: the infinite runs of `pollLoop m` are
exactly the streams calling `m` at every step (any answers); `toInf_spin`,
`toInf_trapLoop`: the silent and the trapping loop have none.
`closeInf_lift_pollLoop`: the module layer's `Shape.closeInf` sees only
infinite runs made through internal recursion, so the closed module whose one
function denotes `pollLoop m` (no internal calls) has none there, while
`toInf` has them. A module semantics that includes infinite runs *inside* a
function needs `toInf` (or the pending calls) of its bodies; that combination
with internal recursion is not defined here.

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

/-- Loops calling different imports forever are different bodies. -/
theorem pollLoop_ne {m₁ m₂ : E.Op} (h : m₁ ≠ m₂) (a : A) (s : S) :
    ((pollLoop m₁ a : BodyM E S T B).run s).run ≠ ((pollLoop m₂ a : BodyM E S T B).run s).run :=
  Silmaril.Proofs.Wasm.Abstract.Loop.pollLoop_ne h a s

/-- Their trap ≈ divergence collapses differ too. -/
theorem collapse_pollLoop_ne {m₁ m₂ : E.Op} (h : m₁ ≠ m₂) (a : A) (s : S) :
    collapse (pollLoop m₁ a : BodyM E S T B) s ≠ collapse (pollLoop m₂ a : BodyM E S T B) s :=
  Silmaril.Proofs.Wasm.Abstract.Loop.collapse_pollLoop_ne h a s

/-- All forever-import loops have the same (empty) denotation. -/
theorem toAFun_pollLoop_eq (m₁ m₂ : E.Op) :
    toAFun (pollLoop m₁ : Hom E S T A B) = toAFun (pollLoop m₂ : Hom E S T A B) := by
  funext s a; rw [toAFun_pollLoop, toAFun_pollLoop]

/-- The converse of `obsCollapse_of_collapse` fails: trap ≈ divergence
equivalent denotations, different collapses. -/
theorem obsCollapse_not_collapse {m₁ m₂ : E.Op} (h : m₁ ≠ m₂) (a : A) (s : S) :
    AFun.ObsEquiv AFun.obsCollapse (toAFun (pollLoop m₁ : Hom E S T A B))
        (toAFun (pollLoop m₂ : Hom E S T A B)) ∧
      collapse (pollLoop m₁ a : BodyM E S T B) ≠ collapse (pollLoop m₂ a : BodyM E S T B) := by
  refine ⟨fun s a => by rw [toAFun_pollLoop_eq m₁ m₂], fun he => ?_⟩
  exact collapse_pollLoop_ne h a s (congrFun he s)

/-- A concrete instance: two loops over `twoImports` with equal denotations
whose collapses differ at every argument and state. -/
theorem exists_obsCollapse_not_collapse :
    ∃ F G : Hom twoImports PUnit.{2} PUnit.{2} PUnit.{2} PUnit.{2},
      toAFun F = toAFun G ∧ ∀ a s, collapse (F a) s ≠ collapse (G a) s :=
  ⟨pollLoop (m := true), pollLoop (m := false), toAFun_pollLoop_eq _ _,
    fun a s => collapse_pollLoop_ne (E := twoImports) (by decide : true ≠ false) a s⟩

/-- The first pending call of `pollLoop m` is `m`. -/
theorem mem_toPending_pollLoop (m : E.Op) (s : S) (a : A) :
    ([], ULift.up m) ∈ toPending (pollLoop m : Hom E S T A B) s a :=
  Silmaril.Proofs.Wasm.Abstract.Loop.mem_toPending_pollLoop m s a

/-- With pending calls, distinct forever-import loops are separated. -/
theorem pollLoop_not_fullCollapseEquiv {m₁ m₂ : E.Op} (h : m₁ ≠ m₂) (a : A) (s : S) :
    ¬ FullCollapseEquiv (pollLoop m₁ : Hom E S T A B) (pollLoop m₂) := fun he =>
  collapse_pollLoop_ne h a s (congrFun ((fullCollapseEquiv_iff _ _).1 he a) s)

/-- The silent and the trapping loop stay identified. -/
theorem spin_fullCollapseEquiv_trapLoop (t : T) :
    FullCollapseEquiv (spin : Hom E S T A B) (trapLoop t) :=
  (fullCollapseEquiv_iff _ _).2 fun a => (collapse_trapLoop t a).symm

/-- The infinite runs of `pollLoop m`: every call is `m`. -/
theorem toInf_pollLoop (m : E.Op) (s : S) (a : A) :
    toInf (pollLoop m : Hom E S T A B) s a = {ω | ∀ n, (ω n).1 = ULift.up m} :=
  Silmaril.Proofs.Wasm.Abstract.Loop.toInf_pollLoop m s a

/-- The trapping loop has no infinite run. -/
theorem toInf_trapLoop (t : T) (s : S) (a : A) :
    toInf (trapLoop t : Hom E S T A B) s a = ∅ :=
  Silmaril.Proofs.Wasm.Abstract.Loop.toInf_trapLoop t s a

/-- The silent loop has no infinite (productive) run. -/
theorem toInf_spin (t : T) (s : S) (a : A) : toInf (spin : Hom E S T A B) s a = ∅ := by
  rw [(spin_fullCollapseEquiv_trapLoop t).toInf, toInf_trapLoop]

/-- `Shape.closeInf` of the closed module whose one function denotes
`pollLoop m` is empty, while `toInf` of the body is not (when `m` can be
answered). -/
theorem closeInf_lift_pollLoop (m : E.Op) [Nonempty (E.Ar m)] (s : S) (a : A) :
    Shape.closeInf (sh := ⟨liftSig E, S, PUnit, fun _ => A, fun _ => B⟩)
        (Shape.lift fun _ => toAFun (pollLoop m : Hom E S T A B)) ⟨⟩ s a = ∅ ∧
      (toInf (pollLoop m : Hom E S T A B) s a).Nonempty := by
  refine ⟨Shape.closeInf_lift _ _ _ _, ?_⟩
  obtain ⟨r⟩ := (inferInstance : Nonempty (E.Ar m))
  exact ⟨fun _ => ⟨⟨m⟩, ⟨r⟩⟩, by rw [toInf_pollLoop]; exact fun _ => rfl⟩

end Silmaril.Wasm.Abstract.Loop
