module

public import Silmaril.Formats.Accept.Defs
public import Silmaril.Semantics.Accept.Bounded.Defs

/-! # Bounded soundness and completeness of acceptor sets

The set-level forms of `Silmaril.Accept.SoundOn`/`CompleteOn` (which are about Bool
checkers): an acceptor set `A` is

* **sound within** a domain `D` for `S` when every accepted input in `D` satisfies `S`;
* **complete within** `D` for `S` when every input of `D` satisfying `S` is accepted.

Typical domains are `Silmaril.Accept.within` a length, a nesting depth or a per-item length
(`Silmaril.Accept.within μ b`). Completeness within a bound is the right claim for an
acceptor whose interface caps its inputs; it does not say that unbounded completeness is
impossible in general, only that this acceptor does not provide it.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Formats.Accept.Lang

universe u

variable {α : Type u}

/-- `A` is sound for `S` on the inputs of `D`. -/
def SoundWithin (D A S : Lang α) : Prop := A ∩ D ⊆ S

/-- `A` is complete for `S` on the inputs of `D`. -/
def CompleteWithin (D A S : Lang α) : Prop := S ∩ D ⊆ A

/-- `A` is exact for `S` on the inputs of `D`. -/
def ExactWithin (D A S : Lang α) : Prop := A ∩ D = S ∩ D

end Silmaril.Formats.Accept.Lang
