module

public import Silmaril.Games.Abstract.ModuleDLog.Defs
public import Silmaril.Games.Abstract.ModuleInf.Defs

/-!
# Closing modules whose trapped calls end the caller: definitions

A call answered by a trap ends its caller at once, with a trap: no call follows it. This module
states that property of an open module and of a closed module, for a predicate `T m n` on the
answers `n` of import calls `m` ("the import trapped") and a predicate `TE f e` on the ends `e`
of the functions `f` ("`e` is a trap end", for instance `End.trap`, or a returned trap answer
keeping its store).

* `TrapLast P Q l`: an element of `l` satisfying `P` is its last element, and then `Q` holds.
* `TrapCall T TE x`: the open call `x` is answered by a trap: an import call answered as `T`
  says, or an internal call whose answer, read as a returning end of the callee, satisfies `TE`.
* `OpenTrapAborts T TE m`: in every behaviour of the open module `m`, a call answered by a trap is
  the last call, and the behaviour then has a trap end.
* `ClosedTrapAborts T TE c`: in every behaviour of the closed module `c`, an import call answered
  by a trap is the last call, and the behaviour then has a trap end.

Theorems in `Silmaril.Games.Abstract.ModuleTrap.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.Shape

open Silmaril.Games

universe u

variable {sh : Shape.{u}}

/-- **An element satisfying `P` is the last one, and then `Q` holds.** -/
def TrapLast {α : Type u} (P : α → Prop) (Q : Prop) (l : List α) : Prop :=
  ∀ u x v, l = u ++ x :: v → P x → v = [] ∧ Q

/-- **The open call is answered by a trap**: an import call whose answer satisfies `T`, or an
internal call whose answer `(b, s')`, as the callee's end `.ret b s'`, satisfies `TE`. -/
def TrapCall (T : (m : sh.E.Op) → sh.E.Ar m → Prop)
    (TE : (f : sh.F) → End sh.S (sh.B f) → Prop) : Call (sh.E ⊕ₛ sh.self) → Prop
  | ⟨.inl m, n⟩ => T m n
  | ⟨.inr ⟨g, _⟩, (b, s')⟩ => TE g (.ret b s')

/-- **In the open module, a trapped call ends the behaviour with a trap end.** -/
def OpenTrapAborts (T : (m : sh.E.Op) → sh.E.Ar m → Prop)
    (TE : (f : sh.F) → End sh.S (sh.B f) → Prop) (m : sh.OpenMod) : Prop :=
  ∀ f s a x, x ∈ m f s a → TrapLast (TrapCall T TE) (TE f x.2) x.1

/-- **In the closed module, a trapped import call ends the behaviour with a trap end.** -/
def ClosedTrapAborts (T : (m : sh.E.Op) → sh.E.Ar m → Prop)
    (TE : (f : sh.F) → End sh.S (sh.B f) → Prop) (c : sh.ClosedMod) : Prop :=
  ∀ f s a y, y ∈ c f s a → TrapLast (fun x : Call sh.E => T x.1 x.2) (TE f y.2) y.1

end Silmaril.Games.Abstract.Shape
