module

public import Silmaril.Semantics.Brookes.Word.Thms
public import Silmaril.Semantics.ConcurrentTrace.Thms

public section

namespace Silmaril.Proofs.Semantics.Brookes.Word.EventSync

open Silmaril.Semantics.ConcurrentTrace
open Silmaril.Semantics.Brookes.Word (Swap)

universe u v

variable {T : Type u} {E : Type v}

/-- The least word congruence is sound for the quotient by swaps in all contexts. -/
theorem swapClass_eq {x y : Word T E} (h : Equivalent x y) :
    Quot.mk (Swap Letter.Independent) x = Quot.mk (Swap Letter.Independent) y := by
  have inContext {a b : FreeMonoid (Letter T E)}
      (hab : ConGen.Rel (Silmaril.Semantics.ConcurrentTrace.Swap (T := T) (E := E)) a b) :
      ∀ pre post : Word T E,
        Quot.mk (Swap Letter.Independent) (pre ++ a.toList ++ post) =
          Quot.mk (Swap Letter.Independent) (pre ++ b.toList ++ post) := by
    induction hab with
    | of a b hs =>
      cases hs with
      | pair hi =>
        intro pre post
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using
          Quot.sound (Swap.adjacent pre post hi)
    | refl => exact fun _ _ => rfl
    | symm _ ih => exact fun pre post => (ih pre post).symm
    | trans _ _ iab ibc => exact fun pre post => (iab pre post).trans (ibc pre post)
    | @mul a b c d _ _ iab icd =>
      intro pre post
      simpa only [FreeMonoid.toList_mul, List.append_assoc] using
        (iab pre (c.toList ++ post)).trans
          (by simpa only [List.append_assoc] using icd (pre ++ b.toList) post)
  simpa only [List.nil_append, List.append_nil] using inContext h [] []

theorem ofWord_eq_of_swap {x y : Word T E} (h : Swap Letter.Independent x y) :
    ofWord x = ofWord y := by
  cases h with
  | adjacent pre post hi =>
    apply (ofWord_eq_iff _ _).mpr
    simpa [List.append_assoc] using Equivalent.swap_in_context hi pre post

end Silmaril.Proofs.Semantics.Brookes.Word.EventSync
