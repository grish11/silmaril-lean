module

public import Silmaril.Formats.PER.Fibers.Defs
public import Silmaril.Formats.PER.Thms
import Silmaril.Proofs.Formats.PER.Fibers

public section

namespace Silmaril.Formats.PER

variable {Key Label Other : Type}

theorem fibers_dom (label : Key → Option Label) (key : Key) :
    (fibers label).Dom key ↔ (label key).isSome :=
  (ofDecoder_dom label key).trans Option.isSome_iff_exists.symm

theorem fibers_class (label : Key → Option Label) {key : Key} {value : Label} (hit : label key = some value) :
    (fibers label).classOf key = {other | label other = some value} := by
  ext other
  change (∃ witness, label key = some witness ∧ label other = some witness) ↔ _
  simp [hit]

theorem fibers_relabel (label : Key → Option Label) (relabel : Label → Other)
    (injective : Function.Injective relabel) : fibers (fun key => (label key).map relabel) = fibers label :=
  Proofs.Formats.PERFibers.fibers_relabel label relabel injective

theorem classes_eq_iff {left right : PER Key} : left.classes = right.classes ↔ left = right :=
  ⟨Proofs.Formats.PERFibers.eq_of_classes, congrArg classes⟩

end Silmaril.Formats.PER
