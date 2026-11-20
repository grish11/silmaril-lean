module

public import Silmaril.Formats.Dasl.Resolve.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl

variable {Name Next Last : Type}

def Named.rename (names : Name → Next) : Named Name → Named Next := Tree.map id names

def Partial.rename (names : Name → Next) : Partial Name → Partial Next := Tree.map (Link.map names) names

/-- Direct image of both lanes: rewrite shallow object links but keep blob bytes. -/
def Store.renameImage (store : Store Name) (names : Name → Next) : Store Next where
  objects next mapped := ∃ old value, store.objects old value ∧ names old = next ∧ Shallow.map names value = mapped
  blobs next bytes := ∃ old, store.blobs old bytes ∧ names old = next

/-- A name map admitting the image of every source binding in the target. This does
not assert that either relation is binding. Use the binding law separately for valid
CAS transport; a noninjective map with unequal output targets cannot satisfy it. -/
structure Renaming (source : Store Name) (target : Store Next) where
  names : Name → Next
  objects : ∀ ⦃name value⦄, source.objects name value → target.objects (names name) (Shallow.map names value)
  blobs : ∀ ⦃name bytes⦄, source.blobs name bytes → target.blobs (names name) bytes

end Silmaril.Formats.Dasl
