module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Generators.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Destructure.Defs

/-! # A computed discriminator and two local label scopes -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Generators.Example

open Paper.EntryLetObstruction.Destructure (U P labels rows)
open SequencingObstruction (Instruction)

abbrev Choice : Ty Empty := Silmaril.coprod U P

/-- Make the request, then discriminate on the retained tagged input. -/
def discriminator : Tm Instruction :=
  .let₁ (.op .tick .unit) (.var 1)

def leftArm : Region Instruction := .br 0 (.var 0)
def rightArm : Region Instruction := .br 1 (.var 0)

/-- The inner entry either takes its own local edge or skips to the outer
product label. -/
def innerEntry : Region Instruction :=
  .case discriminator (.br 0 (.inl (.var 0))) (.br 2 (.var 0))

/-- The inner row consumes its own tagged payload and calls the primitive on
the left before transferring to the outer Unit label. -/
def innerRows : Fin 1 → Region Instruction :=
  fun _ => .case (.var 0) (.br 1 (.op .tick (.var 0))) (.br 2 (.var 0))

def nestedEntry : Region Instruction := .cfg innerEntry 1 innerRows

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Generators.Example
