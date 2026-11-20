module

public import Silmaril.Formats.Dasl.NamedPER.Defs
public import Silmaril.Formats.Dasl.Renaming.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.NamedPER

variable {Name Next Last : Type} {source : Store Name} {target : Store Next} {last : Store Last}
variable {relation : PER (Named Name)} {other : PER (Named Next)} {final : PER (Named Last)}

theorem Respects.id : Respects (Renaming.id source) relation relation := by
  intro left right related
  change relation.rel (left.rename _root_.id) (right.rename _root_.id)
  simpa only [Named.rename_id] using related

theorem Respects.comp {first : Renaming source target} {second : Renaming target last}
    (step : Respects first relation other) (next : Respects second other final) :
    Respects (first.comp second) relation final := by
  intro left right related
  change final.rel (left.rename (second.names ∘ first.names)) (right.rename (second.names ∘ first.names))
  simpa only [Named.rename_comp] using next (step related)

/-- In particular, the forward law gives a map on supported values and their quotient. -/
def Respects.toMap {rename : Renaming source target} (law : Respects rename relation other) :
    PER.Map relation other :=
  ⟨fun tree => ⟨tree.val.rename rename.names, law tree.property⟩, fun _ _ related => law related⟩

theorem fromErasure_equivariant (base : PER Value) : (fromErasure base).Equivariant :=
  fun {_ _ _ _} _ bound rename {left right} ⟨validLeft, validRight, related⟩ =>
    ⟨rename.preserves_valid bound validLeft.2, rename.preserves_valid bound validRight.2, by
      change base.rel left.erase right.erase at related
      change base.rel (left.rename rename.names).erase (right.rename rename.names).erase
      simpa only [Named.erase_rename] using related⟩

theorem partialShallow_rename (rename : Renaming source target) (bound : target.Binding)
    {left right : Partial Name} (related : (partialShallow source).rel left right) :
    (partialShallow target).rel (left.rename rename.names) (right.rename rename.names) :=
  ⟨⟨bound, rename.bindings_subset related.1.2⟩, ⟨bound, rename.bindings_subset related.2.1.2⟩, by
    change (left.rename rename.names).shallow = (right.rename rename.names).shallow
    simpa only [Partial.shallow_rename] using congrArg (Shallow.map rename.names) related.2.2⟩

theorem fromShallow_equivariant : fromShallow.Equivariant :=
  fun {_ _ _ target} _ bound rename {left right} related => by
    change (partialShallow target).rel (left.rename rename.names).embed (right.rename rename.names).embed
    rw [Named.embed_rename, Named.embed_rename]
    exact partialShallow_rename rename bound related

end Silmaril.Formats.Dasl.NamedPER
