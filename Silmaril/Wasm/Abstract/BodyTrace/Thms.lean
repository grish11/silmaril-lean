module

public import Silmaril.Wasm.Abstract.BodyTrace.Defs
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Basic
public import Silmaril.Games.Abstract.FunctionIter.Thms
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Bind
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Iter
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Collapse

/-!
# From interaction-tree bodies to trace-set functions: theorems

* `toAFun_det`: every body denotes an abstract function that is deterministic
  given the history (`AFun.Det`). The environment's answers are inputs, and
  the body's own moves are functions of them.
* `exists_not_denoted`: some abstract function is denoted by no body: a
  nondeterministic choice of result. The bodies are therefore a **restricted
  submodel** of the trace-set functions, contained in the deterministic ones.
  Nondeterministic Wasm behaviour (NaN payloads, relaxed operations) in body
  form changes the interface: the choice becomes an environment event. The
  trace-set functions model it directly as a set of behaviours, so the two
  readings put may/must quantifiers in different places.

* `toAFun_comp`: the denotation maps Kleisli composition of bodies to
  sequencing of trace-set functions, `AFun.seq`, exactly. A trap or divergence
  of the first body ends the run, and a return continues with the second body
  in the state it left.

* `toAFun_iter`: the denotation maps Elgot iteration of bodies to iteration of
  trace-set functions, `AFun.iter`, exactly. No determinism or productivity is
  assumed. Divergence is accounted for in both of its forms: an iteration
  that diverges, and an infinite chain of iterations that each continue
  without an import call (`AFun.IterBeh.spin`), which makes the body loop
  `diverge` although no iteration does. An infinite chain with infinitely
  many import calls is an infinite productive run: it has no finite path, and
  `AFun.iter` gives it no behaviour.
* `obsCollapse_of_collapse`: bodies with equal trap ≈ divergence collapse
  (`Body.collapse`) have trap ≈ divergence equivalent denotations. The
  collapsed observations of `toAFun f` are read off `collapse ∘ f` alone.
* `toAFun_iter_obsCollapse`, `toAFun_iter_of_collapse`: iteration is
  compatible with the trap ≈ divergence observation at the trace level, and
  from collapse-equal loop bodies (with `Body.collapse_iter`, the collapsed
  loops are then equal as bodies too).

Not claimed: injectivity of `toAFun`. It is false: trap payloads are
forgotten (`Silmaril.Wasm.Abstract.BodyLoop.toAFun_not_injective`), and so
are infinite productive runs. Nor the converse of `obsCollapse_of_collapse`,
nor a characterisation of the image (deterministic functions that are
receptive to every answer and total).
-/

public section

namespace Silmaril.Wasm.Abstract.BodyTrace

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body

universe u

/-- Denoted functions are deterministic given the history. -/
theorem toAFun_det {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B) :
    AFun.Det (toAFun f) :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.toAFun_det f

/-- Not every trace-set function is denoted by a body. -/
theorem exists_not_denoted :
    ∃ g : AFun (liftSig Sig.empty.{0}) PUnit.{2} PUnit.{2} (ULift.{1} Bool),
      ∀ (T : Type 1) (f : Hom Sig.empty.{0} PUnit.{2} T PUnit.{2} (ULift.{1} Bool)), toAFun f ≠ g :=
  ⟨Silmaril.Proofs.Wasm.Abstract.BodyTrace.coin,
    fun _ f => Silmaril.Proofs.Wasm.Abstract.BodyTrace.coin_not_denoted f⟩

/-- The denotation maps body composition to trace-set sequencing. -/
theorem toAFun_comp {E : Sig.{u}} {S T A B C : Type (u + 1)} (f : Hom E S T A B)
    (g : Hom E S T B C) :
    toAFun (fun a => f a >>= g) = AFun.seq (toAFun f) (toAFun g) :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.toAFun_comp f g

/-- The paths of a return. -/
theorem path_ret_iff {E : Sig.{u}} {Y : Type (u + 1)} {v : Y} {cs : List (Call E)}
    {r : PathEnd Y} :
    Path (Silmaril.Elgot.ITree.ret v : Silmaril.Elgot.ITree.Tree (SigEv E) Y) cs r ↔
      cs = [] ∧ r = .val v :=
  ⟨Silmaril.Proofs.Wasm.Abstract.BodyTrace.path_ret_inv rfl, by
    rintro ⟨rfl, rfl⟩; exact .ret rfl⟩

/-- A path of a visible event starts with that call, answered by some `n`. -/
theorem path_vis_inv {E : Sig.{u}} {Y : Type (u + 1)} {R : Type u} {e : SigEv E R}
    {k : R → Silmaril.Elgot.ITree.Tree (SigEv E) Y} {cs : List (Call E)} {r : PathEnd Y}
    (h : Path (Silmaril.Elgot.ITree.vis e k) cs r) :
    ∃ n cs', cs = ⟨e.1, cast e.2.symm n⟩ :: cs' ∧ Path (k n) cs' r :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.path_vis_inv h

/-- A body that returns at once denotes its one immediate behaviour. -/
theorem toAFun_of_run_ret {E : Sig.{u}} {S T A B : Type (u + 1)} {f : Hom E S T A B} {s : S}
    {a : A} {v : Except T (B × S)} (h : ((f a).run s).run = Silmaril.Elgot.ITree.ret v) :
    toAFun f s a = {([], endOf (.val v))} :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.toAFun_of_run_ret h

/-- The denotation maps body iteration to trace-set iteration. -/
theorem toAFun_iter {E : Sig.{u}} {S T A B : Type (u + 1)} (F : Hom E S T A (B ⊕ A)) :
    toAFun (Silmaril.Elgot.iter F) = AFun.iter (toAFun F) :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.toAFun_iter F

/-- Bodies with equal trap ≈ divergence collapse have trap ≈ divergence
equivalent denotations. -/
theorem obsCollapse_of_collapse {E : Sig.{u}} {S T A B : Type (u + 1)} {f g : Hom E S T A B}
    (h : ∀ a, collapse (f a) = collapse (g a)) :
    AFun.ObsEquiv AFun.obsCollapse (toAFun f) (toAFun g) :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.obsCollapse_of_collapse h

/-- Loops with trap ≈ divergence equivalent denoted bodies have trap ≈
divergence equivalent denotations. -/
theorem toAFun_iter_obsCollapse {E : Sig.{u}} {S T A B : Type (u + 1)}
    {F G : Hom E S T A (B ⊕ A)}
    (h : AFun.ObsEquiv AFun.obsCollapse (toAFun F) (toAFun G)) :
    AFun.ObsEquiv AFun.obsCollapse (toAFun (Silmaril.Elgot.iter F))
      (toAFun (Silmaril.Elgot.iter G)) := by
  rw [toAFun_iter, toAFun_iter]
  exact AFun.iter_obsCollapse h

/-- Loops whose bodies have equal collapse have trap ≈ divergence equivalent
denotations. -/
theorem toAFun_iter_of_collapse {E : Sig.{u}} {S T A B : Type (u + 1)}
    {F G : Hom E S T A (B ⊕ A)} (h : ∀ a, collapse (F a) = collapse (G a)) :
    AFun.ObsEquiv AFun.obsCollapse (toAFun (Silmaril.Elgot.iter F))
      (toAFun (Silmaril.Elgot.iter G)) :=
  toAFun_iter_obsCollapse (obsCollapse_of_collapse h)

end Silmaril.Wasm.Abstract.BodyTrace
