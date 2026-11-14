module

public import Silmaril.Games.Sig.Defs
public import Silmaril.Semantics.ITree.Thms
public import Silmaril.Semantics.ElgotMonads.Thms
public import Silmaril.SSA.Thesis.Kleisli.Thms

/-!
# Abstract Wasm function bodies: the body monad and its Elgot structure

**Target.** Typed abstract Wasm function bodies form a premonoidal Elgot
category that is a model of λiter (λSSA with iteration), and a quotient of
typed concrete bodies embeds in it. This module builds the abstract half. The
concrete half is a staged roadmap item (`docs/projects/component-semantics.md`).

**The category.** Fix a module environment: imports `E` (a signature: an
import call's argument and its answer type), a module state `S` (memories,
globals and tables consolidated) and a trap type `T`.

* **Objects** are Lean types: typed stack and local interfaces interpreted as
  types of values. Control interfaces with several exits are coproducts
  `A ⊕ B`.
* **Morphisms** `A ⟶ B` are bodies `A → BodyM E S T B`. A body reads and
  writes the module state, may call imports (visible events answered by the
  environment), may trap with a `T`, may diverge silently, and may run
  forever making import calls.
* **Composition** is Kleisli composition, i.e. sequencing.
* **Iteration** is the Elgot iteration of the monad, where `Sum.inl` exits
  and `Sum.inr` loops.

`BodyM E S T` is `StateT S (ExceptT T (ITree (SigEv E)))`. Each layer is a
proved lawful Elgot monad in the library: interaction trees
(`Silmaril.Elgot.ITree.instLawfulElgotMonad`, the weak, tau-insensitive model,
where infinite silent computation is `diverge`), `ExceptT` and `StateT`. So
the Kleisli category of `BodyM` is the Kleisli category of a lawful Elgot
monad on `Type`. That is a premonoidal (Freyd) Elgot category with value
category `Type`: sequencing in the second argument of the premonoidal tensor
fixes the order of effects, and pure maps are central. It is a lawful
categorical model of λiter (`Silmaril.Wasm.Abstract.Body.Thms`).

**Determinism and nondeterminism.** An interaction tree is deterministic given
the environment's answers. Nondeterministic choices (NaN payloads, relaxed
operations, scheduling) are modelled as import-like events answered by the
environment, so a body is strategy-deterministic relative to its inputs.

**Trap ≈ divergence.** `BodyC E S` (`StateT S (ITree (SigEv E))`) has no trap
layer, and `collapse` sends a trap to `diverge`. It is the coarse observation
of the body. Both monads are lawful Elgot monads.

**All behaviours against realisable ones.** Morphisms are arbitrary
mathematical bodies, most of them not the semantics of any Wasm code.
Realisability by concrete bodies is a separate, staged statement.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.Body

open Silmaril.Games

universe u

/-- The events of an import signature: an import, indexed by its answer type. -/
def SigEv (E : Sig.{u}) : Type u → Type u := fun R => {m : E.Op // E.Ar m = R}

/-- The body monad: module state, traps of type `T`, and interaction with the
imports `E` (with divergence and infinite runs). -/
abbrev BodyM (E : Sig.{u}) (S T : Type (u + 1)) : Type (u + 1) → Type (u + 1) :=
  StateT S (ExceptT T (Silmaril.Elgot.ITree.Tree (SigEv E)))

/-- The coarse body monad: traps identified with divergence. -/
abbrev BodyC (E : Sig.{u}) (S : Type (u + 1)) : Type (u + 1) → Type (u + 1) :=
  StateT S (Silmaril.Elgot.ITree.Tree (SigEv E))

/-- A body from `A` to `B`. -/
abbrev Hom (E : Sig.{u}) (S T A B : Type (u + 1)) : Type (u + 1) := A → BodyM E S T B

/-- Call an import: the visible event, answered by the environment. -/
noncomputable def callImport {E : Sig.{u}} {S T : Type (u + 1)} (m : E.Op) :
    BodyM E S T (ULift.{u + 1} (E.Ar m)) :=
  fun s => ExceptT.mk (Silmaril.Elgot.ITree.vis (E := SigEv E) (R := E.Ar m) ⟨m, rfl⟩
    fun n => pure (.ok (ULift.up n, s)))

/-- Trap with `t`. -/
def trap {E : Sig.{u}} {S T A : Type (u + 1)} (t : T) : BodyM E S T A := throw t

/-- Read the module state. -/
def getState {E : Sig.{u}} {S T : Type (u + 1)} : BodyM E S T S := get

/-- Write the module state. -/
def setState {E : Sig.{u}} {S T : Type (u + 1)} (s : S) : BodyM E S T PUnit := set s

/-- Trap ≈ divergence: a trapping run becomes a diverging one. -/
noncomputable def collapse {E : Sig.{u}} {S T A : Type (u + 1)} (x : BodyM E S T A) : BodyC E S A :=
  fun s => (x s).run >>= fun r =>
    match r with
    | .ok p => pure p
    | .error _ => Silmaril.Elgot.ITree.diverge

/-! ## The λiter bridge

λiter's Kleisli model uses the class `Silmaril.Thesis.Elgot.LawfulElgotMonad`,
which has the same laws as `Silmaril.Elgot.LawfulElgotMonad`, stated with its
own `kcomp`. The bridge restates one as the other. -/

/-- The library's iteration operator as λiter's. -/
@[instance_reducible] def thesisIterate (m : Type u → Type u) [Silmaril.Elgot.Iterate m] :
    Silmaril.Thesis.Elgot.Iterate m :=
  ⟨Silmaril.Elgot.iter⟩

end Silmaril.Wasm.Abstract.Body
