module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse

universe u v

variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]
  {n exits : Nat} {β : BoundCtx τ n} {L : LCtx τ}

theorem CheckedTable.toFlat_erase (c : CheckedTable Φ β L) (length : L.length = exits) :
    (c.toFlat length).erase = c.toSSA :=
  Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.toFlat_erase c length

theorem CheckedTable.toFlat_hasType {D : Fin exits → τ} (c : CheckedTable Φ β (List.ofFn D)) :
    (c.toFlat List.length_ofFn).HasType β c.table.types D :=
  Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.toFlat_hasType c

theorem CheckedTable.toFlat_checked (c : CheckedTable Φ β L) (length : L.length = exits) :
    Rank.check (FlatLetCase.localTargets (c.toFlat length)) = true :=
  Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.toFlat_checked c length

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse
