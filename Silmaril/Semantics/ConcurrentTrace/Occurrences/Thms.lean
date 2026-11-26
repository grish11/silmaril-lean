module

public import Silmaril.Semantics.ConcurrentTrace.Occurrences.Defs
import Silmaril.Proofs.Semantics.ConcurrentTrace.Occurrences.Transport

public section

namespace Silmaril.Semantics.ConcurrentTrace

universe u v

variable {T : Type u} {E : Type v}

namespace OccurrencePoset

/-- Transport for a swap sends each of the swapped occurrences to the other's
position and fixes all other positions. -/
def swapIso (pre post : Word T E) {a b : Letter T E} (h : a.Independent b) :
    Iso (ofWord (pre ++ [a, b] ++ post)) (ofWord (pre ++ [b, a] ++ post)) :=
  Proofs.Semantics.ConcurrentTrace.Occurrences.swapIso pre post h

theorem swapIso_apply_val (pre post : Word T E) {a b : Letter T E} (h : a.Independent b)
    (i : Fin (ofWord (pre ++ [a, b] ++ post)).size) :
    ((swapIso pre post h).equiv i).val =
      if i.val = pre.length then pre.length + 1
      else if i.val = pre.length + 1 then pre.length else i.val :=
  Proofs.Semantics.ConcurrentTrace.Occurrences.swapIso_apply_val pre post h i

/-- Equivalent representatives have label- and order-preserving occurrence transport. -/
theorem equivalent_iso {x y : Word T E} (h : Equivalent x y) :
    Nonempty (Iso (ofWord x) (ofWord y)) :=
  Proofs.Semantics.ConcurrentTrace.Occurrences.equivalent_iso h

/-- The occurrence poset of a trace, up to labelled isomorphism. -/
@[expose] def ofTrace (t : Trace T E) : IsoClass T E :=
  Con.liftOn t (fun w => Quotient.mk _ (ofWord w.toList))
    (fun _ _ h => Quotient.sound (equivalent_iso h))

@[simp] theorem ofTrace_ofWord (w : Word T E) :
    ofTrace (ConcurrentTrace.ofWord w) = Quotient.mk _ (ofWord w) := rfl

end OccurrencePoset

end Silmaril.Semantics.ConcurrentTrace
