module

public import Silmaril.Games.Abstract.IterUniform.Defs
public import Mathlib.Data.Set.Finite.Basic

/-!
# Uniformity of iteration along silent, finitely branching maps

`Silmaril.Games.Abstract.IterUniform` proves uniformity of iteration
(`h ; F = G ; [inl, inr ∘ h]` implies `h ; iter F = iter G`) along silent, deterministic,
trap-free, defined maps `h`. Determinism cannot simply be dropped: a silent, total map returning
*any* natural number breaks uniformity (`FullFun.not_iter_uniform_nondet`). That map has
infinitely many behaviours at one state and argument. This topic replaces determinism by finite
branching:

* `FullFun.FinBranch h`: at every state and argument, `h` has finitely many finite behaviours;
* `FullFun.SilentFinNoTrap h`: `h` is silent (`FullFun.Silent`), never traps
  (`FullFun.NoTrap`), has some behaviour (`FullFun.Defined`) and is finitely branching. At one
  state and argument such an `h` may diverge silently, return several results in several
  states, or both.

On triples (`StratOps`), `SilentFinNoTrapT t` also asks for no pending call. On `CanonStrat`,
the condition is that of the representative triple (`CanonStrat.rep`).
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratOps

universe u

variable {E : Sig.{u}} {S A B : Type u}

namespace FullFun

/-- **Finitely branching**: finitely many finite behaviours at every state and argument. -/
def FinBranch (h : FullFun E S A B) : Prop := ∀ s a, (h.1 s a).Finite

/-- **Silent, trap-free, defined and finitely branching**: at each state and argument, a
nonempty finite set of silent behaviours, each a divergence or a return. -/
def SilentFinNoTrap (h : FullFun E S A B) : Prop :=
  Silent h ∧ NoTrap h ∧ Defined h ∧ FinBranch h

end FullFun

namespace StratOps

/-- A triple with no pending call whose full part is `FullFun.SilentFinNoTrap`. -/
def SilentFinNoTrapT (t : ObsTriple E S A B) : Prop :=
  (∀ s a, t.2.1 s a = ∅) ∧ FullFun.SilentFinNoTrap (full t)

end StratOps

namespace CanonStrat

/-- A canonical play object whose representative is `StratOps.SilentFinNoTrapT`. -/
def SilentFinNoTrap (σ : CanonStrat E S A B) : Prop := SilentFinNoTrapT (rep σ)

end CanonStrat

end Silmaril.Games.Abstract
