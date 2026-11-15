module

public import Silmaril.Wasm.Abstract.BodyTrace.Defs
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Basic
public import Silmaril.Games.Abstract.FunctionIter.Thms
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Bind
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Iter
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Collapse
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Faithful
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Inf
public import Silmaril.Games.Abstract.Module.Defs
public import Mathlib.Data.Stream.Init
public import Silmaril.Wasm.Abstract.Body.Thms

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

**A faithful observation.** Finished paths forget infinite productive runs
(and calls whose answer type is empty). Adding the pending calls repairs that:

* `tree_eq_of_obs`: two interaction trees with the same finished paths and
  the same pending calls are equal. No assumption on answer types.
* `faithful_iff`: `toAFun` and `toPending` together determine a body up to
  trap payloads (`erasedRun`), and conversely. So the quotient of bodies by
  this observation is exactly the quotient by trap payloads.
* `fullCollapseEquiv_iff`: up to trap ≈ divergence, the same observation is
  exactly equality of collapses. With `collapse_bind` and `collapse_iter`
  this gives sound adequacy for composition and iteration:
  `FullCollapseEquiv.comp`, `FullCollapseEquiv.iter`. The quotient of
  bodies by `FullCollapseEquiv` is the image of `collapse` in the lawful
  Elgot category of `BodyC`.

**Infinite import streams.** `toInf` collects the infinite productive runs of
a body as streams `Nat → Call`, the representation of the module layer's
`Shape.closeInf`.

* `infPath_iff_pend`, `infPath_iff_streamPrefix`: a stream is an infinite
  run of a tree **iff** each of its finite prefixes (`Shape.StreamPrefix`) is
  pending. No receptivity, compactness or productivity hypothesis: the limit
  exists because partial paths of a tree are unique (determinism given the
  answers). `mem_toInf_iff`, `mem_toInf_iff_streamPrefix`: the same for
  bodies against `toPending`.
* `exists_pend_limit_not_infPath`: determinism is necessary. A family of
  trees (call `i` times, then return), read as one nondeterministic body,
  has every prefix of the forever-calling stream pending, and no member runs
  it.
* Hence the infinite streams are determined by the pending calls
  (`toInf_eq_of_toPending`), so by the faithful observation
  (`toInf_eq_of_faithful`) and by trap ≈ divergence equivalence
  (`FullCollapseEquiv.toInf`).
* `infPath_bind_iff`, `toInf_comp`: compositional lifting through
  sequencing. An infinite run of `f >=> g` is one of `f`, or a finished
  return of `f` (`toAFun f`) followed by an infinite run of `g`, joined with
  `Stream'.appendStream`.

Not claimed: injectivity of `toAFun` alone; a lifting of `toInf` through
iteration (infinitely many iterations, finitely many calls each); and an
operational agreement of `Shape.closeInf` with bodies, which needs the
module-level recursion semantics. It is false: trap payloads are
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

/-- Finished paths and pending calls determine an interaction tree. -/
theorem tree_eq_of_obs {E : Sig.{u}} {Y : Type (u + 1)}
    {t t' : Silmaril.Elgot.ITree.Tree (SigEv E) Y}
    (hp : ∀ cs r, Path t cs r ↔ Path t' cs r) (hq : ∀ cs m, Pend t cs m ↔ Pend t' cs m) :
    t = t' :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.eq_of_sameObs ⟨hp, hq⟩

/-- Finished behaviours and pending calls are faithful up to trap payloads. -/
theorem faithful_iff {E : Sig.{u}} {S T A B : Type (u + 1)} (f g : Hom E S T A B) :
    (toAFun f = toAFun g ∧ toPending f = toPending g) ↔ erasedRun f = erasedRun g :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.faithful_iff f g

/-- Up to trap ≈ divergence, they are faithful up to collapse. -/
theorem fullCollapseEquiv_iff {E : Sig.{u}} {S T A B : Type (u + 1)} (f g : Hom E S T A B) :
    FullCollapseEquiv f g ↔ ∀ a, collapse (f a) = collapse (g a) :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.collapse_faithful_iff f g

/-- The faithful observation determines infinite runs. -/
theorem toInf_eq_of_faithful {E : Sig.{u}} {S T A B : Type (u + 1)} {f g : Hom E S T A B}
    (h : erasedRun f = erasedRun g) : toInf f = toInf g :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.toInf_eq_of_toPending ((faithful_iff f g).2 h).2

/-- Full trap ≈ divergence equivalence is a congruence for composition. -/
theorem FullCollapseEquiv.comp {E : Sig.{u}} {S T A B C : Type (u + 1)} {f f' : Hom E S T A B}
    {g g' : Hom E S T B C} (hf : FullCollapseEquiv f f') (hg : FullCollapseEquiv g g') :
    FullCollapseEquiv (fun a => f a >>= g) (fun a => f' a >>= g') := by
  rw [fullCollapseEquiv_iff] at *
  intro a; simp only [collapse_bind, hf a, hg]

/-- Full trap ≈ divergence equivalence is a congruence for iteration. -/
theorem FullCollapseEquiv.iter {E : Sig.{u}} {S T A B : Type (u + 1)}
    {F G : Hom E S T A (B ⊕ A)} (h : FullCollapseEquiv F G) :
    FullCollapseEquiv (Silmaril.Elgot.iter F) (Silmaril.Elgot.iter G) := by
  rw [fullCollapseEquiv_iff] at *
  intro a; simp only [collapse_iter, h]

/-- A stream is an infinite run iff every finite prefix is pending. -/
theorem infPath_iff_pend {E : Sig.{u}} {Y : Type (u + 1)}
    {t : Silmaril.Elgot.ITree.Tree (SigEv E) Y} {ω : Stream' (Call E)} :
    InfPath t ω ↔ ∀ n, ∃ m, Pend t (ω.take n) m :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.infPath_iff_pend

/-- The same, with the module layer's `StreamPrefix`. -/
theorem infPath_iff_streamPrefix {E : Sig.{u}} {Y : Type (u + 1)}
    {t : Silmaril.Elgot.ITree.Tree (SigEv E) Y} {ω : Stream' (Call E)} :
    InfPath t ω ↔ ∀ l, Shape.StreamPrefix l ω → ∃ m, Pend t l m :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.infPath_iff_streamPrefix

/-- Determinism is necessary: for a family of trees (a nondeterministic body),
pending prefixes have a limit that no member runs. -/
theorem exists_pend_limit_not_infPath :
    ∃ (E : Sig.{0}) (b : Nat → Silmaril.Elgot.ITree.Tree (SigEv E) PUnit.{2})
      (ω : Stream' (Call E)),
      (∀ n, ∃ i m, Pend (b i) (ω.take n) m) ∧ ∀ i ω', ¬ InfPath (b i) ω' :=
  ⟨_, _, _, Silmaril.Proofs.Wasm.Abstract.BodyTrace.union_counterexample⟩

/-- Infinite runs through a bind. -/
theorem infPath_bind_iff {E : Sig.{u}} {Y Z : Type (u + 1)}
    {t : Silmaril.Elgot.ITree.Tree (SigEv E) Z} {k : Z → Silmaril.Elgot.ITree.Tree (SigEv E) Y}
    {ω : Stream' (Call E)} :
    InfPath (t >>= k) ω ↔ InfPath t ω ∨
      ∃ (cs : List (Call E)) (v : Z) (ω' : Stream' (Call E)),
        Path t cs (.val v) ∧ InfPath (k v) ω' ∧ ω = cs ++ₛ ω' :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.infPath_bind_iff

/-- The infinite runs of a body are the limits of its pending calls. -/
theorem mem_toInf_iff {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B) (s : S) (a : A)
    (ω : Nat → Call (liftSig E)) :
    ω ∈ toInf f s a ↔ ∀ n, ∃ m, (Stream'.take n ω, m) ∈ toPending f s a :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.mem_toInf_iff f s a ω

/-- The same, with the module layer's `StreamPrefix`. -/
theorem mem_toInf_iff_streamPrefix {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B)
    (s : S) (a : A) (ω : Nat → Call (liftSig E)) :
    ω ∈ toInf f s a ↔ ∀ l, Shape.StreamPrefix l ω → ∃ m, (l, m) ∈ toPending f s a :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.mem_toInf_iff_streamPrefix f s a ω

/-- Pending calls determine infinite runs. -/
theorem toInf_eq_of_toPending {E : Sig.{u}} {S T A B : Type (u + 1)} {f g : Hom E S T A B}
    (h : toPending f = toPending g) : toInf f = toInf g :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.toInf_eq_of_toPending h

/-- Infinite runs through composition. -/
theorem toInf_comp {E : Sig.{u}} {S T A B C : Type (u + 1)} (f : Hom E S T A B)
    (g : Hom E S T B C) (s : S) (a : A) :
    toInf (fun a => f a >>= g) s a = toInf f s a ∪
      {ω | ∃ (c : List (Call (liftSig E))) (b : B) (s₁ : S) (ω' : Stream' (Call (liftSig E))),
        (c, End.ret b s₁) ∈ toAFun f s a ∧ ω' ∈ toInf g s₁ b ∧ ω = c ++ₛ ω'} :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.toInf_comp f g s a

/-- Trap ≈ divergence equivalent bodies have the same infinite runs. -/
theorem FullCollapseEquiv.toInf {E : Sig.{u}} {S T A B : Type (u + 1)} {f g : Hom E S T A B}
    (h : FullCollapseEquiv f g) : BodyTrace.toInf f = BodyTrace.toInf g :=
  toInf_eq_of_toPending h.2

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
