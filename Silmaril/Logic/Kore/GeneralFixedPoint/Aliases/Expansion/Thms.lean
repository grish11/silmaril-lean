module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.Checking.Defs

@[expose] public section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.Checking

/-- The compiler expands an alias by this very simultaneous substitution.
Local admission of its body and every actual suffices; neither formal namespace
needs a free-polarity restriction. These are executable syntactic Boolean checks,
not assumptions about denotations or preservation. -/
theorem expansion_admissible {scope : Modules.Scope} (d : Declaration)
    {sets objects : Names} {s : String}
    (body : Pattern scope (d.names true) (d.names false) s)
    (setActuals : ∀ i, Pattern scope sets objects (context (d.names true) i))
    (objectActuals : ∀ i, Pattern scope sets objects (context (d.names false) i))
    (admitted : body.admissible = true)
    (setAdmitted : ∀ i, (setActuals i).admissible = true)
    (objectAdmitted : ∀ i, (objectActuals i).admissible = true) :
    (body.substitute setActuals objectActuals).admissible = true :=
  body.admissible_substitute setActuals objectActuals admitted setAdmitted objectAdmitted

end Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.Checking
