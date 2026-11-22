module

public import Silmaril.Calculi.PERConstraints.Patterns.Dasl.Thms

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Patterns.DaslExamples

open Silmaril.Formats Silmaril.Formats.Dasl

inductive Index where
  | narrow
  | wide
  | output

def nonemptyLists {Ref : Type} : Tree.Shape Ref Empty → Prop
  | .list len => 0 < len
  | _ => False

def signature := daslSignature Index (@nonemptyLists Empty)

abbrev Term := Tree Empty Empty

def pair : DaslPattern (@nonemptyLists Empty) 2 := .node (.list 2) Pattern.hole

def narrowRule : Rule signature := ⟨2, fun _ => .narrow, .output, pair⟩

/-- Only the type of the first hole changes, not the shape or plugging. -/
def widenedRule : Rule signature :=
  { narrowRule with holeSort := fun (pos : Fin 2) => if pos = 0 then .wide else .narrow }

def selectedSystem : System := ⟨signature, {narrowRule}⟩

def allNull : Fin 2 → Term := fun _ => .null

def mixed : Fin 2 → Term := fun pos => if pos = 0 then .bool true else .null

def selectedFamily : Family signature
  | .narrow => (PER.equality Term).restrict (· = .null)
  | .wide => PER.universal Term
  | .output => (PER.equality Term).restrict (· = .list 2 allNull)

/-- Each component is full for these guards, but the family is not uniform. -/
def independentlyFull : Family signature
  | .narrow | .wide => PER.universal Term
  | .output => PER.empty Term

end Silmaril.Calculi.PERConstraints.Patterns.DaslExamples
