module

public import Silmaril.Semantics.Relational.Scan.Defs
public import Silmaril.Semantics.Relational.Database.Defs

/-! Observe the existing packed and dependent database presentations at each name. -/

@[expose] public section

namespace Silmaril.Relational.Scan

variable {Name Id Kind : Type*} {Value : Kind → Type*}

/-- Preserve missing names and observe each occupied entry's schema and ordered rows. -/
def observePacked (db : Database.Packed Name (fun s : Schema Id Kind => Table s Value)) :
    Database.Dynamic Name (Observation Id Value) :=
  db.erase Observation.mk

def observeDependent (db : Database.Dependent Name (fun s : Schema Id Kind => Table s Value)) :
    Database.Dynamic Name (Observation Id Value) :=
  observePacked db.pack

end Silmaril.Relational.Scan
