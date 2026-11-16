module

public import Silmaril.Games.Abstract.CloseReach.Defs
import Silmaril.Proofs.Games.Abstract.CloseReach.Basic

/-!
# Closing with reach: theorems

Proofs in `Silmaril.Proofs.Games.Abstract.CloseReach`.

* `close_le_closeR`: reach only adds behaviours; `closeR_mono`: monotone in the
  module and the reach; `resolveR_closeR`: `closeR` is a fixpoint.
* `closeR_eq_close`: reach that `m` already makes (the reached call occurs in a
  behaviour of `m` after the same prefix) adds nothing; `closeR_bot`: no reach
  is `close`.
* **Cuts are exactly reach.** `close_cutMod_eq_closeR`: under

  (a) every reached call has a `Bad` answer,
  (b) no behaviour of the cut module's closure returns a `Bad` answer, and
  (c) reach prefixes are closed (`ReachPrefixClosed`),

  closing the cut module is closing with reach. The two inclusions use the
  hypotheses separately: `closeR_le_close_cutMod` needs only (a);
  `close_cutMod_le_closeR` needs (b) and (c) (`close_cutMod_le_closeR'` takes (b)
  on `closeR` instead).

Each hypothesis is needed for its inclusion. Without (a) a reached call with no
`Bad` answer has no cut behaviour, so its callee's trap is in `closeR` only.
Without (b) a callee returning a `Bad` answer resolves the cut behaviour to a
trap after the callee's import calls, which is not a callee trap. Without (c) a
cut behaviour is resolved by the trap of an earlier internal call in its prefix
(`Subst.intTrap` at that call), which neither `m` nor the reach provides.
-/

public section

namespace Silmaril.Games.Abstract.Shape

universe u

variable {sh : Shape.{u}}

/-- Closing with reach extends closing. -/
theorem close_le_closeR (m : sh.OpenMod) (Rch : sh.ReachRel) : close m ≤ closeR m Rch :=
  Silmaril.Proofs.Games.Abstract.CloseReach.close_le_closeR m Rch

/-- The closed module with reach is a fixpoint of resolution with reach. -/
theorem resolveR_closeR (m : sh.OpenMod) (Rch : sh.ReachRel) :
    resolveR m Rch (closeR m Rch) = closeR m Rch :=
  Silmaril.Proofs.Games.Abstract.CloseReach.resolveR_closeR m Rch

/-- Closing with reach is monotone in the module and the reach. -/
theorem closeR_mono {m m' : sh.OpenMod} {Rch Rch' : sh.ReachRel} (hm : m ≤ m')
    (hr : Rch ≤ Rch') : closeR m Rch ≤ closeR m' Rch' :=
  Silmaril.Proofs.Games.Abstract.CloseReach.closeR_mono hm hr

/-- Reach that the module already makes adds nothing. -/
theorem closeR_eq_close {m : sh.OpenMod} {Rch : sh.ReachRel}
    (hsyn : ∀ x u y, Rch x u y →
      ∃ w ∈ m x.1 x.2.2 x.2.1, ∃ ans rest, w.1 = u ++ ⟨.inr y, ans⟩ :: rest) :
    closeR m Rch = close m :=
  Silmaril.Proofs.Games.Abstract.CloseReach.closeR_eq_close hsyn

/-- With no reach, closing with reach is closing. -/
theorem closeR_bot (m : sh.OpenMod) : closeR m ⊥ = close m :=
  Silmaril.Proofs.Games.Abstract.CloseReach.closeR_bot m

/-- Every reach end is a behaviour of the cut module's closure, when every
reached call has a `Bad` answer. -/
theorem closeR_le_close_cutMod {m : sh.OpenMod} {Rch : sh.ReachRel}
    {Bad : (y : sh.self.Op) → sh.self.Ar y → Prop}
    (hne : ∀ x u y, Rch x u y → ∃ ans, Bad y ans) :
    closeR m Rch ≤ close (cutMod m Rch Bad) :=
  Silmaril.Proofs.Games.Abstract.CloseReach.closeR_le_close_cutMod hne

/-- A cut behaviour resolves only to a reach end, when reach prefixes are closed
and no behaviour of the cut module's closure returns a `Bad` answer. -/
theorem close_cutMod_le_closeR {m : sh.OpenMod} {Rch : sh.ReachRel}
    {Bad : (y : sh.self.Op) → sh.self.Ar y → Prop} (hpc : ReachPrefixClosed m Rch)
    (hbad : ∀ (y : sh.self.Op) c₁ b s',
      (c₁, .ret b s') ∈ close (cutMod m Rch Bad) y.1 y.2.2 y.2.1 → ¬ Bad y (b, s')) :
    close (cutMod m Rch Bad) ≤ closeR m Rch :=
  Silmaril.Proofs.Games.Abstract.CloseReach.close_cutMod_le_closeR hpc hbad

/-- `close_cutMod_le_closeR`, with no `Bad` answer returned by `closeR` instead. -/
theorem close_cutMod_le_closeR' {m : sh.OpenMod} {Rch : sh.ReachRel}
    {Bad : (y : sh.self.Op) → sh.self.Ar y → Prop} (hpc : ReachPrefixClosed m Rch)
    (hbad : ∀ (y : sh.self.Op) c₁ b s',
      (c₁, .ret b s') ∈ closeR m Rch y.1 y.2.2 y.2.1 → ¬ Bad y (b, s')) :
    close (cutMod m Rch Bad) ≤ closeR m Rch :=
  Silmaril.Proofs.Games.Abstract.CloseReach.close_cutMod_le_closeR' hpc hbad

/-- **Cuts are exactly reach.** If every reached call has a `Bad` answer, no
behaviour of the cut module's closure returns one, and reach prefixes are
closed, then closing the cut module is closing with reach. -/
theorem close_cutMod_eq_closeR {m : sh.OpenMod} {Rch : sh.ReachRel}
    {Bad : (y : sh.self.Op) → sh.self.Ar y → Prop}
    (hne : ∀ x u y, Rch x u y → ∃ ans, Bad y ans) (hpc : ReachPrefixClosed m Rch)
    (hbad : ∀ (y : sh.self.Op) c₁ b s',
      (c₁, .ret b s') ∈ close (cutMod m Rch Bad) y.1 y.2.2 y.2.1 → ¬ Bad y (b, s')) :
    close (cutMod m Rch Bad) = closeR m Rch :=
  le_antisymm (close_cutMod_le_closeR hpc hbad) (closeR_le_close_cutMod hne)

end Silmaril.Games.Abstract.Shape
