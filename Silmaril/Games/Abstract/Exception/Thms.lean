module

public import Silmaril.Games.Abstract.Exception.Defs
import Silmaril.Proofs.Games.Abstract.Exception.Basic

/-!
# Exception properties of abstract functions: theorems

* `NoEscape.mono`: fewer runs, fewer escapes.
* `NoEscape.seqX`: if neither part lets an exception escape, the sequence does
  not either.
* `exists_continuation_noEscape_seq_mayEscape`: a continuation that never
  throws does not make the composite exception-free. An exception from the
  first part (a callee) propagates. "No local throw" does not imply "no
  escape".
* `NoEscape.handleX`: a local `try`/`catch` whose handler does not escape
  never escapes, whatever the protected code raises. Raised-and-caught is not
  escaping, so handler transfers remain part of the function's behaviour.
* `NoEscape.under` and `NoEscapeUnder.mono`: no escape survives restriction to
  any import assumption, and a weaker assumption implies a stronger one.

All of these are about executable runs. Concrete Core 3.0 instances, a no-escape
certificate and an escaping `throw`, are in `Silmaril.Wasm.Abstract.Exception`.
-/

public section

namespace Silmaril.Games.Abstract.AFun

open Silmaril.Games

universe u

variable {E : Sig.{u}} {S A R R' X : Type u}

theorem NoEscape.mono {f g : AFun E S A (R ⊕ X)} (h : f ≤ g) (hg : NoEscape g) : NoEscape f :=
  Silmaril.Proofs.Games.Abstract.Exception.noEscape_mono h hg

theorem NoEscape.seqX {f : AFun E S A (R ⊕ X)} {g : AFun E S R (R' ⊕ X)} (hf : NoEscape f)
    (hg : NoEscape g) : NoEscape (AFun.seqX f g) :=
  Silmaril.Proofs.Games.Abstract.Exception.seqX_noEscape hf hg

theorem NoEscape.handleX (f : AFun E S A (R ⊕ X)) {h : AFun E S X (R ⊕ X)} (hh : NoEscape h) :
    NoEscape (AFun.handleX f h) :=
  Silmaril.Proofs.Games.Abstract.Exception.handleX_noEscape f hh

theorem NoEscape.under {f : AFun E S A (R ⊕ X)} (h : NoEscape f) (Q : Call E → Prop) :
    NoEscapeUnder Q f :=
  Silmaril.Proofs.Games.Abstract.Exception.noEscapeUnder_of h Q

theorem NoEscapeUnder.mono {Q Q' : Call E → Prop} (hQ : ∀ y, Q y → Q' y)
    {f : AFun E S A (R ⊕ X)} (h : NoEscapeUnder Q' f) : NoEscapeUnder Q f :=
  Silmaril.Proofs.Games.Abstract.Exception.noEscapeUnder_mono hQ h

open Silmaril.Proofs.Games.Abstract.Exception in
/-- A continuation that never throws does not make the composite
exception-free. -/
theorem exists_continuation_noEscape_seq_mayEscape :
    ∃ (f g : AFun Sig.empty.{0} PUnit.{1} PUnit.{1} (PUnit.{1} ⊕ PUnit.{1})),
      NoEscape g ∧ MayEscape (AFun.seqX f g) ⟨⟩ ⟨⟩ :=
  ⟨raiseNow, retNow, retNow_noEscape, seqX_raise_mayEscape⟩

end Silmaril.Games.Abstract.AFun
