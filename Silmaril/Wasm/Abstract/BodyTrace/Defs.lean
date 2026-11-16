module

public import Silmaril.Wasm.Abstract.Body.Defs
public import Silmaril.Games.Abstract.Function.Defs

/-!
# From interaction-tree bodies to trace-set functions

Abstract functions (`Silmaril.Games.Abstract.AFun`) are arbitrary,
nondeterministic sets of call behaviours. Interaction-tree bodies
(`Silmaril.Wasm.Abstract.Body.BodyM`) are deterministic given the
environment's answers. They are a **restricted submodel**, not a replacement.
This module gives the explicit denotation `toAFun` from bodies to abstract
functions, reading each finite path of the tree (import calls with their
answers, then a return, a trap or silent divergence) as a call behaviour.

`Silmaril.Wasm.Abstract.BodyTrace.Thms` proves that every denoted function is
deterministic given the history, and that not every abstract function is
denoted (a nondeterministic one is not). The image is contained in the
deterministic functions.

**What the denotation forgets.**

* Trap payloads: `AFun` has one `trap` end.
* Infinite productive runs (infinitely many import calls): `AFun` has no
  infinite behaviours, so bodies that differ only on infinite branches may
  have the same denotation.

The denotation is therefore not claimed to be injective.

**Universes.** Bodies take values in `Type (u + 1)` (interaction trees are
large), so the import signature is lifted (`liftSig`) to match.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.BodyTrace

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body

universe u

/-- An import signature lifted one universe up. -/
def liftSig (E : Sig.{u}) : Sig.{u + 1} := ⟨ULift.{u + 1} E.Op, fun m => ULift.{u + 1} (E.Ar m.down)⟩

/-- How a finite path of an interaction tree ends. -/
inductive PathEnd (A : Type (u + 1)) : Type (u + 1)
  /-- Returned `a`. -/
  | val (a : A)
  /-- Diverged silently. -/
  | div

/-- `Path t cs r`: the tree `t` performs the import calls `cs` (with their
answers) and then ends as `r`. -/
inductive Path {E : Sig.{u}} {A : Type (u + 1)} :
    Silmaril.Elgot.ITree.Tree (SigEv E) A → List (Call E) → PathEnd A → Prop
  /-- A return. -/
  | ret {t : Silmaril.Elgot.ITree.Tree (SigEv E) A} {a : A} :
      t = Silmaril.Elgot.ITree.ret a → Path t [] (.val a)
  /-- Silent divergence. -/
  | div {t : Silmaril.Elgot.ITree.Tree (SigEv E) A} :
      t = Silmaril.Elgot.ITree.diverge → Path t [] .div
  /-- An import call answered by `n`, then the rest. -/
  | vis {t : Silmaril.Elgot.ITree.Tree (SigEv E) A} {R : Type u} {e : SigEv E R}
      {k : R → Silmaril.Elgot.ITree.Tree (SigEv E) A} {n : R} {cs : List (Call E)}
      {r : PathEnd A} :
      t = Silmaril.Elgot.ITree.vis e k → Path (k n) cs r →
      Path t (⟨e.1, cast e.2.symm n⟩ :: cs) r

/-- An import call, lifted. -/
def liftCall {E : Sig.{u}} (c : Call E) : Call (liftSig E) := ⟨ULift.up c.1, ULift.up c.2⟩

/-- The end of a body's path as the end of a call behaviour. -/
def endOf {S T B : Type (u + 1)} : PathEnd (Except T (B × S)) → End S B
  | .val (.ok (b, s)) => .ret b s
  | .val (.error _) => .trap
  | .div => .div

/-- The trace-set function denoted by a body. -/
def toAFun {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B) :
    AFun (liftSig E) S A B := fun s a =>
  {x | ∃ cs r, Path ((f a).run s).run cs r ∧ x = (cs.map liftCall, endOf r)}

/-! ## Loops at the tree level -/

/-- Where one iteration of a body leaves the loop: trap or exit (left), or
continue (right). -/
def loopEnd {S T A B : Type (u + 1)} : Except T ((B ⊕ A) × S) → Except T (B × S) ⊕ (A × S)
  | .error e => .inl (.error e)
  | .ok (.inl b, s) => .inl (.ok (b, s))
  | .ok (.inr a, s) => .inr (a, s)

/-- One iteration of a body, as an interaction tree on argument and state. -/
noncomputable def loopTree {E : Sig.{u}} {S T A B : Type (u + 1)} (F : Hom E S T A (B ⊕ A))
    (p : A × S) : Silmaril.Elgot.ITree.Tree (SigEv E) (Except T (B × S) ⊕ (A × S)) :=
  ((F p.1).run p.2).run >>= fun r => pure (loopEnd r)

/-- A finite chain of silent continuations of a loop tree `G` from `x` to the
exit `y`. -/
inductive PureReach {E : Sig.{u}} {X Y : Type (u + 1)}
    (G : X → Silmaril.Elgot.ITree.Tree (SigEv E) (Y ⊕ X)) : X → Y → Prop
  | done {x y} : G x = Silmaril.Elgot.ITree.ret (.inl y) → PureReach G x y
  | step {x x' y} : G x = Silmaril.Elgot.ITree.ret (.inr x') → PureReach G x' y → PureReach G x y

/-! ## Pending calls: the observation that sees infinite productive runs

`toAFun` reads only *finished* paths, so a body that calls imports forever
has no behaviour there (`Silmaril.Wasm.Abstract.Loop.toAFun_pollLoop`). The
pending-call observation records each import call as it is made, before its
answer: "after the calls `cs`, the body calls `m`". This is the prefix
observation of an outcome-tagged trace (`Silmaril.Games.Abstract.Obs.fin s .run`
followed by the next move), and it sees every infinite productive run through
its finite prefixes. It also sees a call to an import whose answer type is
empty, which no finished path does. -/

/-- `Pend t cs m`: the tree `t` performs the import calls `cs` (with their
answers) and then calls `m`. -/
inductive Pend {E : Sig.{u}} {A : Type (u + 1)} :
    Silmaril.Elgot.ITree.Tree (SigEv E) A → List (Call E) → E.Op → Prop
  /-- The next event is a call of `e.1`. -/
  | here {t : Silmaril.Elgot.ITree.Tree (SigEv E) A} {R : Type u} {e : SigEv E R}
      {k : R → Silmaril.Elgot.ITree.Tree (SigEv E) A} :
      t = Silmaril.Elgot.ITree.vis e k → Pend t [] e.1
  /-- An import call answered by `n`, then the rest. -/
  | vis {t : Silmaril.Elgot.ITree.Tree (SigEv E) A} {R : Type u} {e : SigEv E R}
      {k : R → Silmaril.Elgot.ITree.Tree (SigEv E) A} {n : R} {cs : List (Call E)} {m : E.Op} :
      t = Silmaril.Elgot.ITree.vis e k → Pend (k n) cs m →
      Pend t (⟨e.1, cast e.2.symm n⟩ :: cs) m

/-- The pending calls of a body: after the (lifted) calls, the import called. -/
def toPending {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B) :
    S → A → Set (List (Call (liftSig E)) × (liftSig E).Op) := fun s a =>
  {x | ∃ cs m, Pend ((f a).run s).run cs m ∧ x = (cs.map liftCall, ULift.up m)}

/-- Full trap ≈ divergence equivalence: the same finished behaviours up to
trap ≈ divergence, and the same pending calls. -/
def FullCollapseEquiv {E : Sig.{u}} {S T A B : Type (u + 1)} (f g : Hom E S T A B) : Prop :=
  AFun.ObsEquiv AFun.obsCollapse (toAFun f) (toAFun g) ∧ toPending f = toPending g

/-! ## Infinite import streams

An infinite productive run is a stream of answered import calls, in the
representation the module layer uses for `Shape.closeInf` (`Nat → Call`). -/

/-- `InfPath t ω`: the tree `t` performs the infinite stream of answered
import calls `ω`. -/
def InfPath {E : Sig.{u}} {A : Type (u + 1)} (t : Silmaril.Elgot.ITree.Tree (SigEv E) A)
    (ω : Nat → Call E) : Prop :=
  ∃ τ : Nat → Silmaril.Elgot.ITree.Tree (SigEv E) A, τ 0 = t ∧ ∀ n, ∃ (R : Type u)
    (e : SigEv E R) (k : R → Silmaril.Elgot.ITree.Tree (SigEv E) A) (r : R),
    τ n = Silmaril.Elgot.ITree.vis e k ∧ ω n = ⟨e.1, cast e.2.symm r⟩ ∧ τ (n + 1) = k r

/-- The infinite productive runs of a body: their streams of (lifted) import
calls. -/
def toInf {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B) :
    S → A → Set (Nat → Call (liftSig E)) := fun s a =>
  {ω | ∃ ω', InfPath ((f a).run s).run ω' ∧ ω = liftCall ∘ ω'}

/-- Forget a trap's payload. -/
def eraseTrap {T X : Type (u + 1)} : Except T X → Except PUnit.{u + 2} X
  | .ok x => .ok x
  | .error _ => .error ⟨⟩

/-- The interaction tree of a body with trap payloads forgotten. -/
noncomputable def erasedRun {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B) (s : S)
    (a : A) : Silmaril.Elgot.ITree.Tree (SigEv E) (Except PUnit.{u + 2} (B × S)) :=
  ((f a).run s).run >>= fun r => pure (eraseTrap r)

end Silmaril.Wasm.Abstract.BodyTrace
