module

public import Silmaril.Games.Abstract.CanonStrat.Defs

/-!
# Uniformity of iteration along silent maps

Uniformity of iteration says: if `h ; F = G ; [inl, inr ∘ h]` then `h ; iter F = iter G`. It
holds along pure maps (`FullFun.iter_uniform`) and fails along a map that makes an import call
(`FullFun.not_iter_uniform_call`) or traps (`FullFun.not_iter_uniform_trap`). This topic
settles the silent, state-changing maps. The conditions on `h : A' → A`, at every state and
argument:

* `FullFun.Silent h`: no import call. Every finite behaviour has the empty log and there is no
  productive run;
* `AFun.Det h.1`: determinism given the history. For a silent map this means at most one
  behaviour;
* `FullFun.NoTrap h`: no behaviour traps;
* `FullFun.Defined h`: some behaviour.

`FullFun.SilentDetNoTrap h` is the conjunction of the four. Such an `h` either diverges
silently (`([], div)`) or returns one result in one state (`([], ret x t)`), as a function of
the state and argument; it may change the state. `FullFun.SilentTotalDet h` adds that `h`
always returns (`AFun.MustReturn`), the "pure function of state and argument" case.

On triples (`StratOps`), `SilentDetNoTrapT t` and `SilentTotalDetT t` also ask for no pending
call. On `CanonStrat`, the conditions are those of the representative triple (`CanonStrat.rep`).
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratOps

universe u

variable {E : Sig.{u}} {S A B : Type u}

namespace FullFun

/-- **No import call**: every finite behaviour has the empty log, and there is no productive
run. -/
def Silent (h : FullFun E S A B) : Prop :=
  (∀ s a, h.2 s a = ∅) ∧ ∀ s a x, x ∈ h.1 s a → x.1 = []

/-- **No behaviour traps.** -/
def NoTrap (h : FullFun E S A B) : Prop := ∀ s a, ¬ AFun.MayTrap h.1 s a

/-- **Some behaviour** at every state and argument. -/
def Defined (h : FullFun E S A B) : Prop := ∀ s a, (h.1 s a).Nonempty

/-- **Silent, deterministic, trap-free and defined**: at each state and argument, either one
silent divergence or one silent return. -/
def SilentDetNoTrap (h : FullFun E S A B) : Prop :=
  Silent h ∧ AFun.Det h.1 ∧ NoTrap h ∧ Defined h

/-- **Silent, total and deterministic**: at each state and argument, exactly one silent
return, possibly changing the state. -/
def SilentTotalDet (h : FullFun E S A B) : Prop :=
  Silent h ∧ AFun.Det h.1 ∧ ∀ s a, AFun.MustReturn h.1 s a

end FullFun

namespace StratOps

/-- A triple with no pending call whose full part is `FullFun.SilentDetNoTrap`. -/
def SilentDetNoTrapT (t : ObsTriple E S A B) : Prop :=
  (∀ s a, t.2.1 s a = ∅) ∧ FullFun.SilentDetNoTrap (full t)

/-- A triple with no pending call whose full part is `FullFun.SilentTotalDet`. -/
def SilentTotalDetT (t : ObsTriple E S A B) : Prop :=
  (∀ s a, t.2.1 s a = ∅) ∧ FullFun.SilentTotalDet (full t)

end StratOps

namespace CanonStrat

/-- A canonical play object whose representative is `StratOps.SilentDetNoTrapT`. -/
def SilentDetNoTrap (σ : CanonStrat E S A B) : Prop := SilentDetNoTrapT (rep σ)

/-- A canonical play object whose representative is `StratOps.SilentTotalDetT`. -/
def SilentTotalDet (σ : CanonStrat E S A B) : Prop := SilentTotalDetT (rep σ)

end CanonStrat

end Silmaril.Games.Abstract
