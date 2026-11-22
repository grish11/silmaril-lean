module

public import Silmaril.Calculi.PERConstraints.Syntax.Formats.Defs
public import Silmaril.Calculi.PERConstraints.Thms

@[expose] public section
namespace Silmaril.Calculi.PERConstraints

open CategoryTheory Silmaril.Logic.Institution

/-- JSON substitutions translate constraints and pull back PERs on trees. -/
def jsonInstitution (Key : Type) : JsonAtoms Key ⥤ Room.{0,0,0} :=
  jsonSyntax Key ⋙ institution

/-- DASL link-name renamings translate constraints and pull back PERs on shallow trees. -/
def daslInstitution : Type ⥤ Room.{0,0,0} := daslSyntax ⋙ institution

end Silmaril.Calculi.PERConstraints
