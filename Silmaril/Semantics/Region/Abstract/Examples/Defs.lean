module

public import Silmaril.Semantics.Region.Abstract.Named.Defs

@[expose] public section
namespace Silmaril.Semantics.Region.Abstract.Examples

/-- A label-only signature; the numbers name judgments, not machine addresses. -/
abbrev Atom := LabelAtom Unit Unit Nat Unit

def atom (entry : Nat) : Atom := ⟨(), (), entry, ()⟩

def composition : Rule Atom := ⟨{atom 0, atom 1}, atom 2⟩
def rules : Rules Atom := {composition}
def left : RawModel Atom := {atom 0}
def right : RawModel Atom := {atom 1}

end Silmaril.Semantics.Region.Abstract.Examples
