module

public import Silmaril.Calculi.PERConstraints.Thms

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Examples

/-- Keep the two Boolean terms in different classes. -/
def separation : Dictionary Unit Bool := fun _ => some (.distinct [false, true])

/-- Require both equality and distinctness on the same two terms. -/
def conflict : Dictionary Bool Bool := fun key =>
  some (if key then .eq {false, true} else .distinct [false, true])

def booleanRoom : Silmaril.Logic.Institution.Room.{0,0,0} := room ⟨Bool⟩

end Silmaril.Calculi.PERConstraints.Examples
