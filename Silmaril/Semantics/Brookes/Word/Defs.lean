module

public import Silmaril.Semantics.Brookes.Defs

/-! Interpret finite words of an arbitrary alphabet using Brookes commands. -/

@[expose] public section

namespace Silmaril.Semantics.Brookes.Word

universe u v

variable {Letter : Type u} {Store : Type v}

/-- Evaluate in word order, allowing the Brookes environment at joins. -/
def eval (letter : Letter → Command Store) : List Letter → Command Store
  | [] => Command.skip
  | a :: rest => Command.seq (letter a) (eval letter rest)

/-- Observe only contiguous initial-to-final executions. -/
def endpoints (command : Command Store) : Store → Store → Prop :=
  fun s t => command.completes s t ()

/-- One adjacent swap in arbitrary contexts, with independence supplied by the caller. -/
inductive Swap (independent : Letter → Letter → Prop) : List Letter → List Letter → Prop where
  | adjacent (pre post : List Letter) {a b : Letter} (h : independent a b) :
      Swap independent (pre ++ a :: b :: post) (pre ++ b :: a :: post)

/-- Local equations required for interpreting the full open behavior. -/
def Commutes (independent : Letter → Letter → Prop) (letter : Letter → Command Store) : Prop :=
  ∀ ⦃a b⦄, independent a b → Command.seq (letter a) (letter b) = Command.seq (letter b) (letter a)

/-- Local equations required for interpreting just the endpoint relation. -/
def CommutesAtEndpoints (independent : Letter → Letter → Prop)
    (letter : Letter → Command Store) : Prop :=
  ∀ ⦃a b⦄, independent a b →
    endpoints (Command.seq (letter a) (letter b)) = endpoints (Command.seq (letter b) (letter a))

end Silmaril.Semantics.Brookes.Word
