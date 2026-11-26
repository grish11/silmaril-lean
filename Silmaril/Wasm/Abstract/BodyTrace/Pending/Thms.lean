module

public import Silmaril.Wasm.Abstract.BodyTrace.Defs
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Faithful

public section

namespace Silmaril.Wasm.Abstract.BodyTrace

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body

universe u

/-- A pending observation of a visible node either stops at its request or
follows its continuation after an answer. -/
theorem Pend.vis_cases {E : Sig.{u}} {Y : Type (u + 1)} {R : Type u} {e : SigEv E R}
    {k : R → Silmaril.Elgot.ITree.Tree (SigEv E) Y} {cs : List (Call E)} {m : E.Op}
    (h : Pend (Silmaril.Elgot.ITree.vis e k) cs m) :
    (cs = [] ∧ m = e.1) ∨
      ∃ n cs', cs = ⟨e.1, cast e.2.symm n⟩ :: cs' ∧ Pend (k n) cs' m :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.pend_vis_inv h

end Silmaril.Wasm.Abstract.BodyTrace
