module

public import Silmaril.Games.Abstract.IterUniformFin.Defs
public import Silmaril.Games.Abstract.IterUniform.Thms
import Silmaril.Proofs.Games.Abstract.IterUniformFin.Uniform
import Silmaril.Proofs.Games.Abstract.IterUniformFin.Lift
import Silmaril.Proofs.Games.Abstract.IterUniformFin.Compare

/-!
# Uniformity of iteration along silent, finitely branching maps: theorems

Proofs in `Silmaril.Proofs.Games.Abstract.IterUniformFin`.

**Uniformity** (`….Uniform`, `….Lift`): if `h ; F = G ; [inl, inr ∘ h]` then
`h ; iter F = iter G`, finite behaviours (with divergence) and productive runs, for `h` silent,
trap-free, defined and finitely branching, but possibly nondeterministic:

* `FullFun.iter_uniform_silent_finite`: full observations;
* `StratOps.iterT_uniform_silent_finite`: triples, the map also without pending calls;
* `CanonStrat.iter_uniform_silent_finite`: canonical play objects, through the representative
  triple.

Nothing is assumed of `F` or `G`. The hypothesis only says that the behaviours of `G` at
`(s, a)`, with `h` applied to each continuation, are the union over the returns `(x, t)` of `h`
at `(s, a)` of the behaviours of `F` at `(t, x)`, with a silent divergence where `h` may
diverge.

* **From `F` to `G`** no finiteness is needed. Each step of a run of `F` from a return of `h`
  at `(s, a)` is a step of `G` from `(s, a)` into a point at which the next point of `F` is
  again a return of `h`. Infinite runs follow by dependent choice.
* **From `G` to `F`** a step of `G` into `(s₁, a₁)`, followed by any return `(x₁, t₁)` of `h`
  there, is a step of `F` into `(x₁, t₁)` from *some* return of `h` at the start. Finite runs of
  `G` map to runs of `F` from their end backwards. For an infinite chain of `G`, the returns of
  `h` along it form levels in which every element has a parent. With finite branching the
  levels are finite, and König's lemma gives an infinite path, a chain of `F`. Without it the
  levels can be infinite with no infinite path (`FullFun.not_iter_uniform_infinite`).

**Comparison with determinism** (`….Compare`):

* `FullFun.SilentDetNoTrap.silentFinNoTrap`, `StratOps.SilentDetNoTrapT.silentFinNoTrapT`: a
  silent deterministic map is finitely branching (one behaviour), so these theorems generalise
  `FullFun.iter_uniform_silent` and its lifts;
* `FullFun.not_iter_uniform_infinite`: the counterexample of `FullFun.not_iter_uniform_nondet`
  is silent, trap-free and defined, and not finitely branching. So finite branching cannot be
  dropped. Silence, trap-freedom and definedness cannot be dropped either: the counterexamples
  `FullFun.not_iter_uniform_call_needs_silent`, `FullFun.not_iter_uniform_trap_needs_noTrap`
  and `FullFun.not_iter_uniform_undefined` are deterministic, hence finitely branching.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratOps

universe u

variable {E : Sig.{u}} {S A A' B : Type u}

/-! ## Uniformity -/

/-- **Uniformity of iteration along a silent, trap-free, defined, finitely branching map**: if
`h ; F = G ; [inl, inr ∘ h]` then `h ; iter F = iter G`. -/
theorem FullFun.iter_uniform_silent_finite {h : FullFun E S A' A} {F : FullFun E S A (B ⊕ A)}
    {G : FullFun E S A' (B ⊕ A')} (hh : FullFun.SilentFinNoTrap h)
    (hFG : FullFun.seq h F =
      FullFun.seq G (FullFun.case (FullFun.pure.map Sum.inl) (h.map Sum.inr))) :
    FullFun.seq h (FullFun.iter F) = FullFun.iter G :=
  Silmaril.Proofs.Games.Abstract.IterUniformFin.iter_uniform hh hFG

/-- **Uniformity of iteration for triples** along a silent, trap-free, defined, finitely
branching map with no pending call. -/
theorem StratOps.iterT_uniform_silent_finite {h : ObsTriple E S A' A}
    {F : ObsTriple E S A (B ⊕ A)} {G : ObsTriple E S A' (B ⊕ A')} (hh : SilentFinNoTrapT h)
    (hFG : seqT h F = seqT G (caseT (mapT pureT Sum.inl) (mapT h Sum.inr))) :
    seqT h (iterT F) = iterT G :=
  Silmaril.Proofs.Games.Abstract.IterUniformFin.iterT_uniform hh hFG

/-- **Uniformity of iteration for canonical play objects** along a silent, trap-free, defined,
finitely branching map. -/
theorem CanonStrat.iter_uniform_silent_finite {h : CanonStrat E S A' A}
    {F : CanonStrat E S A (B ⊕ A)} {G : CanonStrat E S A' (B ⊕ A')}
    (hh : CanonStrat.SilentFinNoTrap h)
    (hFG : CanonStrat.seq h F =
      CanonStrat.seq G (CanonStrat.case (CanonStrat.map CanonStrat.pure Sum.inl)
        (CanonStrat.map h Sum.inr))) :
    CanonStrat.seq h (CanonStrat.iter F) = CanonStrat.iter G :=
  Silmaril.Proofs.Games.Abstract.IterUniformFin.canon_iter_uniform hh hFG

/-! ## Comparison with determinism -/

/-- A silent, deterministic, trap-free, defined map is finitely branching. -/
theorem FullFun.SilentDetNoTrap.silentFinNoTrap {h : FullFun E S A' A}
    (hh : FullFun.SilentDetNoTrap h) : FullFun.SilentFinNoTrap h :=
  Silmaril.Proofs.Games.Abstract.IterUniformFin.silentFinNoTrap_of_silentDetNoTrap hh

theorem StratOps.SilentDetNoTrapT.silentFinNoTrapT {t : ObsTriple E S A' A}
    (ht : SilentDetNoTrapT t) : SilentFinNoTrapT t :=
  Silmaril.Proofs.Games.Abstract.IterUniformFin.silentFinNoTrapT_of_silentDetNoTrapT ht

theorem CanonStrat.SilentDetNoTrap.silentFinNoTrap {σ : CanonStrat E S A' A}
    (hσ : CanonStrat.SilentDetNoTrap σ) : CanonStrat.SilentFinNoTrap σ :=
  StratOps.SilentDetNoTrapT.silentFinNoTrapT hσ

/-- **Infinitely branching**: return any natural number, silently, always, keeping the state.
Silent, trap-free and defined, but not finitely branching, and uniformity fails. -/
theorem FullFun.not_iter_uniform_infinite (E : Sig.{u}) :
    let h : FullFun E PUnit.{u + 1} PUnit.{u + 1} (ULift.{u} ℕ) :=
      (fun s _ => {y | ∃ n : ℕ, y = ([], End.ret ⟨n⟩ s)}, fun _ _ => ∅)
    let F : FullFun E PUnit.{u + 1} (ULift.{u} ℕ) (PUnit.{u + 1} ⊕ ULift.{u} ℕ) :=
      (fun s n => {y | y = ([], End.ret (.inl ⟨⟩) s) ∨
        ∃ m < n.down, y = ([], End.ret (.inr ⟨m⟩) s)}, fun _ _ => ∅)
    let G : FullFun E PUnit.{u + 1} PUnit.{u + 1} (PUnit.{u + 1} ⊕ PUnit.{u + 1}) :=
      (fun s _ => {y | y = ([], End.ret (.inl ⟨⟩) s) ∨ y = ([], End.ret (.inr ⟨⟩) s)},
        fun _ _ => ∅)
    FullFun.Silent h ∧ FullFun.NoTrap h ∧ FullFun.Defined h ∧ ¬ FullFun.FinBranch h ∧
      FullFun.seq h F = FullFun.seq G (FullFun.case (FullFun.pure.map Sum.inl) (h.map Sum.inr)) ∧
      ([], End.div) ∈ (FullFun.iter G).1 ⟨⟩ ⟨⟩ ∧
      ([], End.div) ∉ (FullFun.seq h (FullFun.iter F)).1 ⟨⟩ ⟨⟩ :=
  Silmaril.Proofs.Games.Abstract.IterUniformFin.not_iter_uniform_infinite E

end Silmaril.Games.Abstract
