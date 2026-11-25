module

public import Silmaril.Courses.Cambridge.L3.Concrete.Lexicon
public import Silmaril.Courses.Cambridge.L3.RecordFields

/-! The same ordered-field grammar serves record expressions and record types. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Concrete

open Silmaril.Courses.Cambridge.Concrete

variable {α β : Type}

/-- Consume a nonempty sequence of fields through the closing brace. -/
def readFields (read : List Token → Option (α × List Token)) (separator : Punct) :
    Nat → List Token → Option (List (Label × α) × List Token)
  | fuel + 1, .variable label :: rest => do
    let rest ← expect (.punct separator) rest
    let (value, tail) ← read rest
    match tail with
    | .punct .closeBrace :: tail => return ([(label, value)], tail)
    | .punct .comma :: tail =>
      let (fields, tail) ← readFields read separator fuel tail
      return ((label, value) :: fields, tail)
    | _ => none
  | _, _ => none

abbrev buildFields := @RecordLabels.ofEntries α

def readFieldList (read : List Token → Option (α × List Token)) (separator : Punct)
    (fuel : Nat) : List Token → Option (List (Label × α) × List Token)
  | .punct .closeBrace :: rest => some ([], rest)
  | tokens => readFields read separator fuel tokens

def readRecord (make : (labels : RecordLabels) → (labels.Index → α) → α)
    (read : List Token → Option (α × List Token)) (separator : Punct) (fuel : Nat)
    (tokens : List Token) : Option (α × List Token) := do
  let (entries, tail) ← readFieldList read separator fuel tokens
  let ⟨labels, fields⟩ ← buildFields entries
  return (make labels fields, tail)

abbrev recordEntries := @RecordLabels.entries α

/-- Print fields and the closing brace, with commas between fields. -/
def fieldsTokens (separator : Punct) : List (Label × List Token) → List Token
  | [] => [.punct .closeBrace]
  | (label, value) :: rest =>
    [.variable label, .punct separator] ++ value ++
      (if rest.isEmpty then [.punct .closeBrace] else .punct .comma :: fieldsTokens separator rest)

end Silmaril.Courses.Cambridge.L3.Concrete
