module

public import Silmaril.Games.Abstract.SessionLink.Defs
public import Mathlib.Logic.Equiv.Prod

/-!
# Linking sessions: literal associativity and units (definitions)

`SessionCat` proves the category laws of `SessionLink.linkS` on sessions (`threadS`), under
determinism hypotheses. This topic states them on the triples themselves, as literal equalities
after transporting the store along an equivalence.

**Transport along a store equivalence.** `mapStore e t`, for `e : S ≃ S'`, is the triple `t` on the
store `S'`: at the store `s'` it behaves as `t` at `e.symm s'`, and the final store of a return is
mapped by `e` (`mapEnd`). Logs, pending calls and productive streams are unchanged.

**Dropping plain traps.** `dropTrap t` removes the plain traps (`End.trap`) from the finished
behaviours of `t`, keeping its pending calls and productive streams. `linkS` ignores the plain
traps of its server, and the identity client `SessionCat.idS` adds no end of its own, so
`linkS t idS` is `dropTrap (sat t)` on the store `S × PUnit`.

Theorems in `Silmaril.Games.Abstract.SessionLinkAssoc.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.SessionLinkAssoc

open Silmaril.Games

universe u

variable {E : Sig.{u}} {S S' A B : Type u}

/-- The end of a round with its final store mapped by `e`. -/
def mapEnd (e : S → S') : End S B → End S' B
  | .ret b s => .ret b (e s)
  | .trap => .trap
  | .div => .div

/-- **Transport a triple along a store equivalence**: at `s'`, behave as `t` at `e.symm s'`, the
final store of a return mapped by `e`. -/
def mapStore (e : S ≃ S') (t : ObsTriple E S A B) : ObsTriple E S' A B :=
  (fun s a => (fun x => (x.1, mapEnd e x.2)) '' t.1 (e.symm s) a,
    fun s a => t.2.1 (e.symm s) a,
    fun s a => t.2.2 (e.symm s) a)

/-- The finished behaviours of `t` other than plain traps; pending calls and streams kept. -/
def dropTrap (t : ObsTriple E S A B) : ObsTriple E S A B :=
  (fun s a => {x | x ∈ t.1 s a ∧ x.2 ≠ End.trap}, t.2.1, t.2.2)

/-! ## Counterexamples for the unit laws before saturation -/

/-- A server that traps plainly: `linkS trapT idS` drops its trap. -/
def trapT : ObsTriple E PUnit.{u + 1} PUnit.{u + 1} (PUnit.{u + 1} ⊕ PUnit.{u + 1}) :=
  (fun _ _ => {([], End.trap)}, fun _ _ => ∅, fun _ _ => ∅)

/-- A client that calls once and diverges, with no pending calls: it is not saturated. -/
def callDivT : ObsTriple (sig1 PUnit.{u + 1} PUnit.{u + 1}) PUnit.{u + 1} PUnit.{u + 1}
    (PUnit.{u + 1} ⊕ PUnit.{u + 1}) :=
  (fun _ _ => {([⟨PUnit.unit, .inl PUnit.unit⟩], End.div)}, fun _ _ => ∅, fun _ _ => ∅)

end Silmaril.Games.Abstract.SessionLinkAssoc
