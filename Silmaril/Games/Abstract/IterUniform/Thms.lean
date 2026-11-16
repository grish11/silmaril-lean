module

public import Silmaril.Games.Abstract.IterUniform.Defs
public import Silmaril.Games.Abstract.CanonStrat.Thms
import Silmaril.Proofs.Games.Abstract.IterUniform.Basic
import Silmaril.Proofs.Games.Abstract.IterUniform.Uniform
import Silmaril.Proofs.Games.Abstract.IterUniform.Lift
import Silmaril.Proofs.Games.Abstract.IterUniform.Counter

/-!
# Uniformity of iteration along silent maps: theorems

Proofs in `Silmaril.Proofs.Games.Abstract.IterUniform`.

**The maps** (`….Basic`):

* `FullFun.silentDetNoTrap_iff`: `h` is silent, deterministic, trap-free and defined iff at
  every state and argument it has no productive run and its finite behaviours are exactly
  `{([], div)}` or exactly `{([], ret x t)}`;
* `FullFun.silentTotalDet_iff`: `h` is silent, total and deterministic iff its finite behaviours
  are exactly `{([], ret x t)}`. The result `x` and the new state `t` may depend on the state
  and the argument;
* `FullFun.SilentTotalDet.silentDetNoTrap`: the second condition implies the first.

**Uniformity** (`….Uniform`, `….Lift`): if `h ; F = G ; [inl, inr ∘ h]` then
`h ; iter F = iter G`, finite behaviours (with divergence) and productive runs, for

* `FullFun.iter_uniform_silent`: `h` silent, deterministic, trap-free and defined. `h` may
  change the state, and it may diverge silently;
* `FullFun.iter_uniform_silentTotalDet`: `h` silent, total and deterministic;
* `StratOps.iterT_uniform_silent`, `StratOps.iterT_uniform_silentTotalDet`: triples, the map
  also without pending calls;
* `CanonStrat.iter_uniform_silent`, `CanonStrat.iter_uniform_silentTotalDet`: canonical play
  objects, through the representative triple.

The proof threads the state through the chain. Where `h` returns `(x, t)` at `(s, a)`, `F` at
`(t, x)` is `G` at `(s, a)` with each continuation `inr a₁` in `s₁` replaced by `h (s₁, a₁)`.
A continuation into a point where `h` diverges becomes a divergence of `F`. Where `h`
diverges, `G` only diverges silently or continues silently to such points, so `iter G`
diverges silently. A productive chain of `G` never reaches such a point. Infinite chains of
`F` lift to `G` by dependent choice, using determinism of `h` at each step.

**Each condition is needed** (`….Counter`). Dropping one of the four conditions and keeping
the other three, uniformity fails:

* `FullFun.not_iter_uniform_call_needs_silent`: one import call; deterministic and total
  (from `FullFun.not_iter_uniform_call`);
* `FullFun.not_iter_uniform_trap_needs_noTrap`: always trap; silent, deterministic, defined
  (from `FullFun.not_iter_uniform_trap`);
* `FullFun.not_iter_uniform_nondet`: return any `n : ℕ`; silent, always returning and
  state-preserving, but not deterministic. With `F n` exiting or continuing with some `m < n`
  and `G` exiting or continuing with its argument, `iter G` diverges silently and
  `h ; iter F` never diverges (every chain of `F` decreases). A run of `G` would need the
  choices of `h` along it to be made consistently, one after the other;
* `FullFun.not_iter_uniform_undefined`: no behaviour; silent, deterministic, never traps or
  diverges. Both sides of the hypothesis are empty, but `iter G` diverges silently.

None of the four conditions can be dropped.
Totality (always returning) is not needed: silent divergence of `h` is allowed.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratOps

universe u

variable {E : Sig.{u}} {S A A' B : Type u}

/-! ## The maps -/

/-- **Silent, deterministic, trap-free and defined**: one silent divergence or one silent
return at each state and argument, and no productive run. -/
theorem FullFun.silentDetNoTrap_iff {h : FullFun E S A' A} :
    FullFun.SilentDetNoTrap h ↔
      ∀ s a, h.2 s a = ∅ ∧
        (h.1 s a = {([], End.div)} ∨ ∃ x t, h.1 s a = {([], End.ret x t)}) :=
  Silmaril.Proofs.Games.Abstract.IterUniform.silentDetNoTrap_iff

/-- **Silent, total and deterministic**: one silent return at each state and argument, possibly
changing the state, and no productive run. -/
theorem FullFun.silentTotalDet_iff {h : FullFun E S A' A} :
    FullFun.SilentTotalDet h ↔ ∀ s a, h.2 s a = ∅ ∧ ∃ x t, h.1 s a = {([], End.ret x t)} :=
  Silmaril.Proofs.Games.Abstract.IterUniform.silentTotalDet_iff

theorem FullFun.SilentTotalDet.silentDetNoTrap {h : FullFun E S A' A}
    (hh : FullFun.SilentTotalDet h) : FullFun.SilentDetNoTrap h :=
  Silmaril.Proofs.Games.Abstract.IterUniform.silentDetNoTrap_of_silentTotalDet hh

/-! ## Uniformity -/

/-- **Uniformity of iteration along a silent, deterministic, trap-free, defined map**: if
`h ; F = G ; [inl, inr ∘ h]` then `h ; iter F = iter G`. -/
theorem FullFun.iter_uniform_silent {h : FullFun E S A' A} {F : FullFun E S A (B ⊕ A)}
    {G : FullFun E S A' (B ⊕ A')} (hh : FullFun.SilentDetNoTrap h)
    (hFG : FullFun.seq h F =
      FullFun.seq G (FullFun.case (FullFun.pure.map Sum.inl) (h.map Sum.inr))) :
    FullFun.seq h (FullFun.iter F) = FullFun.iter G :=
  Silmaril.Proofs.Games.Abstract.IterUniform.iter_uniform hh hFG

/-- **Uniformity of iteration along a silent, total, deterministic map.** -/
theorem FullFun.iter_uniform_silentTotalDet {h : FullFun E S A' A} {F : FullFun E S A (B ⊕ A)}
    {G : FullFun E S A' (B ⊕ A')} (hh : FullFun.SilentTotalDet h)
    (hFG : FullFun.seq h F =
      FullFun.seq G (FullFun.case (FullFun.pure.map Sum.inl) (h.map Sum.inr))) :
    FullFun.seq h (FullFun.iter F) = FullFun.iter G :=
  FullFun.iter_uniform_silent hh.silentDetNoTrap hFG

theorem StratOps.SilentTotalDetT.silentDetNoTrapT {t : ObsTriple E S A' A}
    (ht : SilentTotalDetT t) : SilentDetNoTrapT t :=
  ⟨ht.1, ht.2.silentDetNoTrap⟩

/-- **Uniformity of iteration for triples** along a silent, deterministic, trap-free, defined
map with no pending call. -/
theorem StratOps.iterT_uniform_silent {h : ObsTriple E S A' A} {F : ObsTriple E S A (B ⊕ A)}
    {G : ObsTriple E S A' (B ⊕ A')} (hh : SilentDetNoTrapT h)
    (hFG : seqT h F = seqT G (caseT (mapT pureT Sum.inl) (mapT h Sum.inr))) :
    seqT h (iterT F) = iterT G :=
  Silmaril.Proofs.Games.Abstract.IterUniform.iterT_uniform hh hFG

/-- **Uniformity of iteration for triples** along a silent, total, deterministic map with no
pending call. -/
theorem StratOps.iterT_uniform_silentTotalDet {h : ObsTriple E S A' A}
    {F : ObsTriple E S A (B ⊕ A)} {G : ObsTriple E S A' (B ⊕ A')} (hh : SilentTotalDetT h)
    (hFG : seqT h F = seqT G (caseT (mapT pureT Sum.inl) (mapT h Sum.inr))) :
    seqT h (iterT F) = iterT G :=
  StratOps.iterT_uniform_silent hh.silentDetNoTrapT hFG

/-- **Uniformity of iteration for canonical play objects** along a silent, deterministic,
trap-free, defined map. -/
theorem CanonStrat.iter_uniform_silent {h : CanonStrat E S A' A} {F : CanonStrat E S A (B ⊕ A)}
    {G : CanonStrat E S A' (B ⊕ A')} (hh : CanonStrat.SilentDetNoTrap h)
    (hFG : CanonStrat.seq h F =
      CanonStrat.seq G (CanonStrat.case (CanonStrat.map CanonStrat.pure Sum.inl)
        (CanonStrat.map h Sum.inr))) :
    CanonStrat.seq h (CanonStrat.iter F) = CanonStrat.iter G :=
  Silmaril.Proofs.Games.Abstract.IterUniform.canon_iter_uniform hh hFG

/-- **Uniformity of iteration for canonical play objects** along a silent, total,
deterministic map. -/
theorem CanonStrat.iter_uniform_silentTotalDet {h : CanonStrat E S A' A}
    {F : CanonStrat E S A (B ⊕ A)} {G : CanonStrat E S A' (B ⊕ A')}
    (hh : CanonStrat.SilentTotalDet h)
    (hFG : CanonStrat.seq h F =
      CanonStrat.seq G (CanonStrat.case (CanonStrat.map CanonStrat.pure Sum.inl)
        (CanonStrat.map h Sum.inr))) :
    CanonStrat.seq h (CanonStrat.iter F) = CanonStrat.iter G :=
  CanonStrat.iter_uniform_silent (StratOps.SilentTotalDetT.silentDetNoTrapT hh) hFG

/-! ## Each condition is needed -/

/-- **Not silent**: a map making one import call, deterministic and total. -/
theorem FullFun.not_iter_uniform_call_needs_silent :
    ∃ (E : Sig.{0}) (h : FullFun E PUnit PUnit PUnit) (G : FullFun E PUnit PUnit (PUnit ⊕ PUnit)),
      AFun.Det h.1 ∧ (∀ s a, AFun.MustReturn h.1 s a) ∧ FullFun.NoTrap h ∧ FullFun.Defined h ∧
      ¬ FullFun.Silent h ∧
      FullFun.seq h G = FullFun.seq G (FullFun.case (FullFun.pure.map Sum.inl) (h.map Sum.inr)) ∧
      FullFun.seq h (FullFun.iter G) ≠ FullFun.iter G :=
  Silmaril.Proofs.Games.Abstract.IterUniform.not_iter_uniform_call

/-- **May trap**: an always-trapping map, silent, deterministic and defined. -/
theorem FullFun.not_iter_uniform_trap_needs_noTrap :
    ∃ (E : Sig.{0}) (h : FullFun E PUnit PUnit PUnit) (G : FullFun E PUnit PUnit (PUnit ⊕ PUnit)),
      FullFun.Silent h ∧ AFun.Det h.1 ∧ FullFun.Defined h ∧ ¬ FullFun.NoTrap h ∧
      FullFun.seq h G = FullFun.seq G (FullFun.case (FullFun.pure.map Sum.inl) (h.map Sum.inr)) ∧
      FullFun.seq h (FullFun.iter G) ≠ FullFun.iter G :=
  Silmaril.Proofs.Games.Abstract.IterUniform.not_iter_uniform_trap

/-- **Nondeterministic**: return any natural number, silently, always, keeping the state. -/
theorem FullFun.not_iter_uniform_nondet (E : Sig.{u}) :
    let h : FullFun E PUnit.{u + 1} PUnit.{u + 1} (ULift.{u} ℕ) :=
      (fun s _ => {y | ∃ n : ℕ, y = ([], End.ret ⟨n⟩ s)}, fun _ _ => ∅)
    let F : FullFun E PUnit.{u + 1} (ULift.{u} ℕ) (PUnit.{u + 1} ⊕ ULift.{u} ℕ) :=
      (fun s n => {y | y = ([], End.ret (.inl ⟨⟩) s) ∨
        ∃ m < n.down, y = ([], End.ret (.inr ⟨m⟩) s)}, fun _ _ => ∅)
    let G : FullFun E PUnit.{u + 1} PUnit.{u + 1} (PUnit.{u + 1} ⊕ PUnit.{u + 1}) :=
      (fun s _ => {y | y = ([], End.ret (.inl ⟨⟩) s) ∨ y = ([], End.ret (.inr ⟨⟩) s)},
        fun _ _ => ∅)
    FullFun.Silent h ∧ (∀ s a, AFun.MustReturn h.1 s a) ∧ AFun.StatePreserving h.1 ∧
      ¬ AFun.Det h.1 ∧
      FullFun.seq h F = FullFun.seq G (FullFun.case (FullFun.pure.map Sum.inl) (h.map Sum.inr)) ∧
      ([], End.div) ∈ (FullFun.iter G).1 ⟨⟩ ⟨⟩ ∧
      ([], End.div) ∉ (FullFun.seq h (FullFun.iter F)).1 ⟨⟩ ⟨⟩ :=
  Silmaril.Proofs.Games.Abstract.IterUniform.not_iter_uniform_nondet E

/-- **Undefined**: a map with no behaviour, silent, deterministic, never trapping or
diverging. -/
theorem FullFun.not_iter_uniform_undefined (E : Sig.{u}) :
    let h : FullFun E PUnit.{u + 1} PUnit.{u + 1} PUnit.{u + 1} := (fun _ _ => ∅, fun _ _ => ∅)
    let G : FullFun E PUnit.{u + 1} PUnit.{u + 1} (PUnit.{u + 1} ⊕ PUnit.{u + 1}) :=
      FullFun.pure.map Sum.inr
    FullFun.Silent h ∧ AFun.Det h.1 ∧ FullFun.NoTrap h ∧ (∀ s a, ¬ AFun.MayDiv h.1 s a) ∧
      ¬ FullFun.Defined h ∧
      FullFun.seq h G = FullFun.seq G (FullFun.case (FullFun.pure.map Sum.inl) (h.map Sum.inr)) ∧
      ([], End.div) ∈ (FullFun.iter G).1 ⟨⟩ ⟨⟩ ∧
      (FullFun.seq h (FullFun.iter G)).1 ⟨⟩ ⟨⟩ = ∅ :=
  Silmaril.Proofs.Games.Abstract.IterUniform.not_iter_uniform_undefined E

end Silmaril.Games.Abstract
