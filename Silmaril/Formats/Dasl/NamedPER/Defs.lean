module

public import Silmaril.Formats.Dasl.Renaming.Defs
public import Silmaril.Formats.PER.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.NamedPER

variable {Name Next : Type} {source : Store Name} {target : Store Next}

/-- Named trees use the existing `Formats.PER`; support need not be total. -/
def onStore (store : Store Name) (relation : PER (Named Name)) : PER (Named Name) :=
  relation.restrict (fun tree => store.Binding ∧ tree.embed.bindings.Subset store)

abbrev Family := (Name : Type) → Store Name → PER (Named Name)

/-- The forward preservation law; no reflection or injectivity is implied. -/
def Respects (rename : Renaming source target) (relation : PER (Named Name))
    (other : PER (Named Next)) : Prop :=
  ∀ ⦃left right⦄, relation.rel left right → other.rel (left.rename rename.names) (right.rename rename.names)

def Family.Equivariant (family : Family) : Prop :=
  ∀ {Name Next : Type} {source : Store Name} {target : Store Next},
    source.Binding → target.Binding → ∀ rename : Renaming source target,
      Respects rename (family Name source) (family Next target)

def fromErasure (relation : PER Value) : Family :=
  fun _ store => onStore store (relation.pull Named.erase)

/-- Equality of shallow views after checking all supplied witnesses. Opaque edges
are not asserted bindings and need not be resolvable. -/
def partialShallow (store : Store Name) : PER (Partial Name) :=
  PER.kernelOn (fun tree => store.Binding ∧ tree.bindings.Subset store) Partial.shallow

/-- Name-sensitive equality of shallow views on valid full expansions. -/
def fromShallow : Family := fun _ store => (partialShallow store).pull Named.embed

end Silmaril.Formats.Dasl.NamedPER
