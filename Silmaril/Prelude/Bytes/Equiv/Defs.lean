module

public import Silmaril.Prelude.Bytes.Defs

/-! # Kernel bytes up to the bytes they hold (`≈`)

Two kernel byte strings are **equivalent**, `a ≈ b`, iff they hold the same bytes:
`a.toList = b.toList`. This is Lean's `HasEquiv`, through a `Setoid KBytes` instance, so
`Quotient`, `Setoid.refl`/`symm`/`trans` and `calc` chains with `≈` work as usual.

The relation is about the **represented bytes only**:

* It is independent of the representation: a leaf, a rope, a slice, a written tree and the
  canonical tree of the same bytes are all equivalent, while being different terms. `≈` does
  not imply `=` (structural equality), and the theorems do not claim it.
* It is defined for every tree, including trees whose cached lengths are wrong (`wf = false`)
  and leaves with digits beyond their length: `toList` reads a leaf through its own length and a
  node through its children, ignoring the cached node length.

Operations defined by `toList` alone (`++`, `toByteArray`) respect `≈` for all trees. Operations
that use the cached lengths (`len`, `read`, `readLE`, `get?`, `slice`, `canon`, writes) respect
it on trees with correct cached lengths (`wf`); on malformed trees they may not
(`Silmaril.Prelude.Bytes.Equiv.Thms` has a counterexample). The congruence theorems state
exactly these hypotheses.
-/

@[expose] public section

namespace Silmaril.KBytes

/-- The same bytes. -/
def Equiv (a b : KBytes) : Prop := a.toList = b.toList

instance instSetoid : Setoid KBytes where
  r := Equiv
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

end Silmaril.KBytes
