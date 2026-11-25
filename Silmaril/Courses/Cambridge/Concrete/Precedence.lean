module

public import Silmaril.Courses.Cambridge.Concrete.Lexer

/-! Token readers shared by the course's concrete precedence profiles. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concrete

abbrev Reader (α : Type) := List Token → Option (α × List Token)

def readComplete {α : Type} (read : Nat → Reader α) (tokens : List Token) : Option α := do
  let (value, []) ← read (tokens.length + 1) tokens | none
  return value

/-- Preserve the accepted interpretation of every explicitly grouped input.
The precedence reader also handles complete inputs with omitted grouping. -/
def readWithPrecedence {α : Type} (grouped ordinary : Nat → Reader α)
    (tokens : List Token) : Option α :=
  (readComplete grouped tokens).orElse (fun _ => readComplete ordinary tokens)

theorem readWithPrecedence_of_grouped {α : Type} {grouped ordinary : Nat → Reader α}
    {tokens : List Token} {value : α}
    (h : grouped (tokens.length + 1) tokens = some (value, [])) :
    readWithPrecedence grouped ordinary tokens = some value := by
  simp [readWithPrecedence, readComplete, h]

def infixOnce {α : Type} (read : Reader α) (op : Punct) (make : α → α → α) :
    Reader α := fun tokens => do
  let (left, tail) ← read tokens
  match expect (.punct op) tail with
  | none => return (left, tail)
  | some rest =>
    let (right, tail) ← read rest
    return (make left right, tail)

def chainRight {α : Type} (read : Reader α) (op : Punct) (make : α → α → α) :
    Nat → Reader α
  | 0, _ => none
  | fuel + 1, tokens => do
    let (left, tail) ← read tokens
    match expect (.punct op) tail with
    | none => return (left, tail)
    | some rest =>
      let (right, tail) ← chainRight read op make fuel rest
      return (make left right, tail)

def readApplication {α : Type} (read : Reader α) (startsArgument : List Token → Bool)
    (make : α → α → α) (fuel : Nat) : Reader α := fun tokens => do
  let (fn, tail) ← read tokens
  more fuel fn tail
where
  more : Nat → α → Reader α
    | 0, _, _ => none
    | fuel + 1, fn, tail =>
      if startsArgument tail then do
        let (arg, rest) ← read tail
        more fuel (make fn arg) rest
      else some (fn, tail)

/-- In a lambda annotation an arrow followed by another type and delimiter
belongs to the annotation. The last arrow separates the term body. -/
def readBinderType {α : Type} (read : Reader α) (arrow : α → α → α) : Nat → Reader α
  | 0, _ => none
  | fuel + 1, tokens => do
    let (domain, tail) ← read tokens
    let tail ← expect (.punct .arrow) tail
    match readBinderType read arrow fuel tail with
    | some (codomain, rest) => return (arrow domain codomain, rest)
    | none => return (domain, tail)

/-- Keyword-led forms may begin an operand. Juxtaposition after an already
read function uses the smaller argument category. -/
def startsArgument : List Token → Bool
  | .number _ :: _ | .punct .minus :: .number _ :: _
  | .keyword .trueK :: _ | .keyword .falseK :: _ | .keyword .skip :: _
  | .variable _ :: _ | .punct .openP :: _ | .punct .deref :: _ => true
  | _ => false

end Silmaril.Courses.Cambridge.Concrete
