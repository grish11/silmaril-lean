module

public import Silmaril.SSA.Isotope.LetIter.Monadic.Reindex.Structured.Defs
public import Silmaril.Semantics.ITree.Reindex.Thms

import Silmaril.Proofs.SSA.Isotope.LetIter.Monadic.Reindex.Structured.Transport

/-! # Naturality of structured LetIter calls -/

public section

namespace Silmaril.Isotope.LetIter.Reindex.Structured

open Silmaril.Isotope.Semantics Silmaril.Elgot
open PaperExpression.Source.FreeTree.Response.Structured (Event Lifted toSmall)

universe u

variable {α : Type u} {V W : α → Type u}

theorem request_inverse {Φ : Type u} [HasTy Φ (Ty α)]
    (e : ∀ a, V a ≃ W a) (q : ITree.Request (Event (Φ := Φ) V)) :
    (signatureEquiv (fun a => (e a).symm)).request ((signatureEquiv e).request q) = q :=
  Silmaril.Proofs.LetIter.Reindex.Structured.request_inverse e q

theorem toSmall_natural (e : ∀ a, V a ≃ W a) (A : Ty α) (x : Ty.denote (Lifted V) A) :
    toSmall W A (typeEquiv (liftedEquiv e) A x) = typeEquiv e A (toSmall V A x) :=
  Silmaril.Proofs.LetIter.Reindex.Structured.toSmall_natural e A x

/-- The primitive square for the visible-call interpretation holds for any
family of base-carrier equivalences. -/
theorem call_natural {Φ : Type u} [HasTy Φ (Ty α)]
    (e : ∀ a, V a ≃ W a) (f : Φ) (x : Ty.denote (Lifted V) (instrSrc f)) :
    (signatureEquiv (Φ := Φ) e).tree (typeEquiv (liftedEquiv e) (instrTrg f))
      ((callInstructions V).eval f x) =
    (callInstructions W).eval f (typeEquiv (liftedEquiv e) (instrSrc f) x) :=
  Silmaril.Proofs.LetIter.Reindex.Structured.call_natural e f x

end Silmaril.Isotope.LetIter.Reindex.Structured
