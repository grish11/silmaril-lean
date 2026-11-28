module

public import Silmaril.Calculi.PERConstraints.Interval.Thms
public import Silmaril.Calculi.PERConstraints.Examples.Defs

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.IntervalExamples

open Silmaril.Formats

inductive Term where
  | first | middle | last

/-- The full PER interval on a carrier. -/
def full (α : Type) : Bounds α := ⟨PER.empty α, PER.universal α, fun _ _ h => h.elim⟩

def pairOnly (left right : Term) : PER Term := (PER.universal Term).restrict (· ∈ ({left, right} : Set Term))

def eitherPair : CNF Term := CNF.ofOr {.eq {.first, .middle}, .eq {.middle, .last}}

def separateEnds : CNF Term := CNF.ofOr {.distinct [.first, .last]}

def joinFirstMiddle : PER Term := PER.kernel fun
  | Term.last => true
  | _ => false

def joinMiddleLast : PER Term := PER.kernel fun
  | Term.first => true
  | _ => false

def separateBools : CNF Bool := Dictionary.toCNF Examples.separation

def requireFalse : CNF Bool := CNF.ofOr {.eq {false}}

def collapse : Bool → Unit := fun _ => ()

end Silmaril.Calculi.PERConstraints.IntervalExamples
