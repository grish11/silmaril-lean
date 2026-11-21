module

public import Silmaril.Formats.PER.Defs

@[expose] public section

namespace Silmaril.Formats.PER

variable {Key Label : Type}

/-- Only successful lookups have a class. Labels need not be members, or even
have the same type as members. -/
abbrev fibers (label : Key → Option Label) : PER Key := ofDecoder label

def classOf (relation : PER Key) (member : Key) : Set Key := {other | relation.rel member other}

/-- The extensional family of nonempty classes of a partial partition. -/
def classes (relation : PER Key) : Set (Set Key) := {group | ∃ member, relation.Dom member ∧ relation.classOf member = group}

end Silmaril.Formats.PER
