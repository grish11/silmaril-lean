module

public import Silmaril.Games.Abstract.ModuleTrap.Defs
import Silmaril.Proofs.Games.Abstract.ModuleTrap.Basic

/-!
# Closing modules whose trapped calls end the caller: theorems

For an import-trap predicate `T` and a trap-end predicate `TE` that holds of `End.trap` and not
of `End.div`:

* **Finished behaviours** (`close_trapAborts`): if in every behaviour of the open module `m` a
  call answered by a trap (an import call satisfying `T`, or an internal call whose answer is a
  trap end) is the last one and the behaviour has a trap end (`OpenTrapAborts T TE m`), then
  the same holds of the import calls of `close m` (`ClosedTrapAborts T TE (close m)`). The
  proof is least-fixpoint induction: a returning callee whose log has a trapped import call
  returns a trap end, so the internal call is itself trapped and ends its caller.
* **Prefixes and descents** (`substPre_noTrap`, `descends_noTrap`, `descPath_noTrap`): a resolved
  prefix of untrapped calls, and the import calls made along a descent, have no trapped import
  call: the internal calls in them return, and a trapped call in a prefix would be followed by
  another call.
* **Divergence** (`closeD_div_noTrap`, `closeDLog_div_noTrap`): a divergent behaviour has no
  trapped import call, given that the logged local divergence `LDL` has no trapped open call.
* **Productive streams** (`closeInfL_noTrap`): no productive stream of `closeInfL m mi` has a
  trapped import call, given that the productive open runs `mi` have no trapped open call.
* `TrapLast` bookkeeping: `trapLast_nil`, `trapLast_of_forall`, `TrapLast.forall_not`,
  `TrapLast.mono`, `TrapLast.append_left`, `TrapLast.append_right`, `TrapLast.append`,
  `TrapLast.cons`, `TrapLast.head`, `TrapLast.tail`, `trapLast_concat`, `trapLast_singleton`;
  `streamConcat_mem`: every element of a concatenation lies in one of its segments.

Proofs in `Silmaril.Proofs.Games.Abstract.ModuleTrap`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.Shape

open Silmaril.Games

universe u

variable {sh : Shape.{u}}

/-! ## `TrapLast` -/

section TrapLast

variable {α : Type u} {P : α → Prop} {Q Q' : Prop} {l l₁ l₂ : List α} {x y : α}

theorem trapLast_nil : TrapLast P Q [] := Silmaril.Proofs.Games.Abstract.ModuleTrap.trapLast_nil

theorem trapLast_of_forall (h : ∀ x ∈ l, ¬ P x) : TrapLast P Q l :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.trapLast_of_forall h

/-- With `Q` false, no element satisfies `P`. -/
theorem TrapLast.forall_not (h : TrapLast P Q l) (hQ : ¬ Q) : ∀ x ∈ l, ¬ P x :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.TrapLast.forall_not h hQ

theorem TrapLast.mono (h : TrapLast P Q l) (hQ : Q → Q') : TrapLast P Q' l :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.TrapLast.mono h hQ

/-- An element followed by another does not satisfy `P`. -/
theorem TrapLast.append_left (h : TrapLast P Q (l₁ ++ y :: l₂)) : ∀ x ∈ l₁, ¬ P x :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.TrapLast.append_left h

theorem TrapLast.append_right (h : TrapLast P Q (l₁ ++ l₂)) : TrapLast P Q l₂ :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.TrapLast.append_right h

theorem TrapLast.append (h₁ : ∀ x ∈ l₁, ¬ P x) (h₂ : TrapLast P Q l₂) :
    TrapLast P Q (l₁ ++ l₂) :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.TrapLast.append h₁ h₂

theorem TrapLast.cons (hx : P x → l = [] ∧ Q) (h : TrapLast P Q l) : TrapLast P Q (x :: l) :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.TrapLast.cons hx h

theorem TrapLast.head (h : TrapLast P Q (x :: l)) (hx : P x) : l = [] ∧ Q := h [] x l rfl hx

theorem TrapLast.tail (h : TrapLast P Q (x :: l)) : TrapLast P Q l :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.TrapLast.tail h

theorem trapLast_concat (h₁ : ∀ x ∈ l, ¬ P x) (h₂ : P y → Q) : TrapLast P Q (l ++ [y]) :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.trapLast_concat h₁ h₂

theorem trapLast_singleton (h : P y → Q) : TrapLast P Q [y] :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.trapLast_singleton h

/-- Every element of a concatenation lies in one of its segments. -/
theorem streamConcat_mem {l : Nat → List α} {ω : Nat → α} (h : StreamConcat l ω) (k : Nat) :
    ∃ i, ω k ∈ l i :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.streamConcat_mem h k

end TrapLast

variable {T : (m : sh.E.Op) → sh.E.Ar m → Prop} {TE : (f : sh.F) → End sh.S (sh.B f) → Prop}

/-! ## Finished behaviours -/

/-- **The closure of a trap-aborting open module is trap-aborting.** -/
theorem close_trapAborts {m : sh.OpenMod} (hm : OpenTrapAborts T TE m)
    (htrap : ∀ g, TE g .trap) (hdiv : ∀ g, ¬ TE g .div) : ClosedTrapAborts T TE (close m) :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.close_trapAborts hm htrap hdiv

/-! ## Prefixes and descents -/

/-- **A resolved prefix of untrapped calls has no trapped import call.** -/
theorem substPre_noTrap {c : sh.ClosedMod} (hc : ClosedTrapAborts T TE c)
    {u : List (Call (sh.E ⊕ₛ sh.self))} {q : List (Call sh.E)} (h : SubstPre c u q)
    (hu : ∀ x ∈ u, ¬ TrapCall T TE x) : ∀ x ∈ q, ¬ T x.1 x.2 :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.substPre_noTrap hc h hu

theorem descends_noTrap {m : sh.OpenMod} {c : sh.ClosedMod} (hm : OpenTrapAborts T TE m)
    (hc : ClosedTrapAborts T TE c) {x y : sh.self.Op} {q : List (Call sh.E)}
    (h : Descends m c x q y) : ∀ e ∈ q, ¬ T e.1 e.2 :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.descends_noTrap hm hc h

theorem descPath_noTrap {m : sh.OpenMod} {c : sh.ClosedMod} (hm : OpenTrapAborts T TE m)
    (hc : ClosedTrapAborts T TE c) {x z : sh.self.Op} {qs : List (Call sh.E)}
    (h : DescPath m c x qs z) : ∀ e ∈ qs, ¬ T e.1 e.2 :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.descPath_noTrap hm hc h

/-! ## Divergence -/

/-- **A divergent behaviour of `closeD` has no trapped import call.** -/
theorem closeD_div_noTrap {m : sh.OpenMod} (hm : OpenTrapAborts T TE m)
    (htrap : ∀ g, TE g .trap) (hdiv : ∀ g, ¬ TE g .div) {f : sh.F} {s : sh.S} {a : sh.A f}
    {y : CallBeh sh.E sh.S (sh.B f)} (hy : y ∈ closeD m f s a) (hd : y.2 = .div) :
    ∀ e ∈ y.1, ¬ T e.1 e.2 :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.closeD_div_noTrap hm htrap hdiv hy hd

/-- **A divergent behaviour of `closeDLog` has no trapped import call**, when the logged local
divergence has no trapped open call. -/
theorem closeDLog_div_noTrap {m : sh.OpenMod}
    {LDL : sh.self.Op → List (Call (sh.E ⊕ₛ sh.self)) → Prop} (hm : OpenTrapAborts T TE m)
    (htrap : ∀ g, TE g .trap) (hdiv : ∀ g, ¬ TE g .div)
    (hL : ∀ z u, LDL z u → ∀ x ∈ u, ¬ TrapCall T TE x) {f : sh.F} {s : sh.S} {a : sh.A f}
    {y : CallBeh sh.E sh.S (sh.B f)} (hy : y ∈ closeDLog m LDL f s a) (hd : y.2 = .div) :
    ∀ e ∈ y.1, ¬ T e.1 e.2 :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.closeDLog_div_noTrap hm htrap hdiv hL hy hd

/-! ## Productive streams -/

/-- **A productive stream of `closeInfL` has no trapped import call**, when the productive open
runs have no trapped open call. -/
theorem closeInfL_noTrap {m : sh.OpenMod} {mi : OpenInf sh} (hm : OpenTrapAborts T TE m)
    (htrap : ∀ g, TE g .trap) (hdiv : ∀ g, ¬ TE g .div)
    (hmi : ∀ f s a ν, ν ∈ mi f s a → ∀ i, ¬ TrapCall T TE (ν i)) {f : sh.F} {s : sh.S}
    {a : sh.A f} {ω : Nat → Call sh.E} (hω : ω ∈ closeInfL m mi f s a) (k : Nat) :
    ¬ T (ω k).1 (ω k).2 :=
  Silmaril.Proofs.Games.Abstract.ModuleTrap.closeInfL_noTrap hm htrap hdiv hmi hω k

end Silmaril.Games.Abstract.Shape
