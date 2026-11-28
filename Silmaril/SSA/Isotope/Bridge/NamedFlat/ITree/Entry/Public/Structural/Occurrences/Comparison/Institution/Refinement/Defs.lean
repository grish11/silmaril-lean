module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Institution.Thms

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {S : OpcodeSignature}
  {exits : List K} {fields : K → List V}

/-- Reverse only the direction of comparison. The original store and the
ordered output interface are shared. -/
def Endpoints.swap (point : Endpoints V K S) : Endpoints V K S :=
  ⟨point.right, point.left, point.initial⟩

/-- The exact gate and independent decodings are available in either
direction, regardless of the outcome of refinement. -/
def Admission.swap {point : Endpoints V K S} (a : Admission point exits fields) :
    Admission point.swap exits fields :=
  ⟨a.rightType, a.leftType, a.outputs, a.right, a.left,
    by
      exact (a.right.checkOccurrenceComparison?_isSome_iff a.left).mpr
        ((a.left.checkOccurrenceComparison?_isSome_iff a.right).mp a.checked).symm,
    a.rightPacket, a.leftPacket, a.rightSeed, a.leftSeed⟩

def Admission.toSentence {point : Endpoints V K S} (a : Admission point exits fields) :
    Sentence S exits fields :=
  ⟨point, ⟨a⟩⟩

def Sentence.swap (φ : Sentence S exits fields) : Sentence S exits fields :=
  ⟨φ.val.swap, φ.property.elim fun a => ⟨a.swap⟩⟩

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution
