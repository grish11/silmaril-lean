module

public import Silmaril.Games.Abstract.FunctionIter.Defs
public import Silmaril.Games.Abstract.Function.Defs
import Silmaril.Proofs.Games.Abstract.FunctionIter.Basic
import Silmaril.Proofs.Games.Abstract.FunctionIter.Unfold

/-!
# Iteration of abstract functions: theorems

* `iter_unfold` (**the fixpoint law**): `iter f = seq f (case pure (iter f))`. One
  iteration runs; `inl b` exits through `pure`, `inr a'` continues with `iter f`. It holds
  with no hypothesis on `f`, for every end: a trap or divergence of the first iteration ends
  the loop, and an infinite silent chain (`spin`) is its first iteration followed by the
  shifted chain.
* `iter_mono`: iteration is monotone in the loop body.
* `iter_obsCollapse`: trap ≈ divergence is a congruence for iteration. A
  trapping iteration and a diverging one end the loop with the same collapsed
  observation, and an infinite silent chain is made of returns, which the
  collapse keeps exactly.
* `iter_obsId`: the full (sensitive) observation is a congruence too, since it
  is equality (`obsEquiv_id_iff`).
* Three shapes of divergence and abort: a body that only continues silently
  iterates to silent divergence, `([], div)` (`iter_continue`), although it
  never diverges itself; a body that always traps iterates to a trap
  (`iter_trap`); and a body each of whose behaviours makes an import call and
  continues has **no** finite iterated behaviour (`iter_productive`): its runs
  are infinite and productive, which `AFun` does not represent.
-/

public section

namespace Silmaril.Games.Abstract.AFun

open Silmaril.Games

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-- **The fixpoint law**: one iteration, then exit (`inl`) or iterate again (`inr`). -/
theorem iter_unfold (f : AFun E S A (B ⊕ A)) : iter f = seq f (case pure (iter f)) :=
  Silmaril.Proofs.Games.Abstract.FunctionIter.iter_unfold f

/-- Iteration is monotone. -/
theorem iter_mono {f g : AFun E S A (B ⊕ A)} (h : f ≤ g) : iter f ≤ iter g :=
  Silmaril.Proofs.Games.Abstract.FunctionIter.iter_mono h

/-- Trap ≈ divergence is a congruence for iteration. -/
theorem iter_obsCollapse {f g : AFun E S A (B ⊕ A)} (h : ObsEquiv obsCollapse f g) :
    ObsEquiv obsCollapse (iter f) (iter g) :=
  Silmaril.Proofs.Games.Abstract.FunctionIter.iter_obsCollapse h

/-- The full observation is a congruence for iteration. -/
theorem iter_obsId {f g : AFun E S A (B ⊕ A)} (h : ObsEquiv obsId f g) :
    ObsEquiv obsId (iter f) (iter g) := fun s a => by
  have : f = g := funext fun s => funext fun a => by simpa [obsId] using h s a
  rw [this]

/-- Silent continuation forever is silent divergence. -/
theorem iter_continue {f : AFun E S A (B ⊕ A)} (hf : ∀ s a, f s a = {([], .ret (.inr a) s)})
    (s : S) (a : A) : iter f s a = {([], .div)} :=
  Silmaril.Proofs.Games.Abstract.FunctionIter.iter_continue hf s a

/-- A body that always traps iterates to a trap. -/
theorem iter_trap {f : AFun E S A (B ⊕ A)} (hf : ∀ s a, f s a = {([], .trap)})
    (s : S) (a : A) : iter f s a = {([], .trap)} :=
  Silmaril.Proofs.Games.Abstract.FunctionIter.iter_trap hf s a

/-- A body that always calls an import and continues has no finite iterated
behaviour. -/
theorem iter_productive {f : AFun E S A (B ⊕ A)}
    (hf : ∀ s a x, x ∈ f s a → x.1 ≠ [] ∧ ∃ a' s', x.2 = .ret (.inr a') s') (s : S) (a : A) :
    iter f s a = ∅ :=
  Silmaril.Proofs.Games.Abstract.FunctionIter.iter_productive hf s a

end Silmaril.Games.Abstract.AFun
