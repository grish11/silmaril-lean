module

public import Silmaril.Formats.Dasl.Resolve.Defs
import Silmaril.Proofs.Formats.Dasl.Resolve

public section

namespace Silmaril.Formats.Dasl

open Silmaril.Semantics.Naming

variable {Name : Type} {store : Store Name}

theorem Expands.unique (bound : store.Binding) {source : Shallow Name} {left right : Named Name}
    (first : Expands store source left) (second : Expands store source right) : left = right :=
  Proofs.Formats.Dasl.expands_unique bound first second

theorem fullNames_binding (bound : store.Binding) : Binding (FullNames store) :=
  Proofs.Formats.Dasl.full_binding bound

theorem valueNames_binding (bound : store.Binding) : Binding (ValueNames store) :=
  Proofs.Formats.Dasl.value_binding bound

theorem Expands.shallow_eq {source : Shallow Name} {target : Named Name}
    (expanded : Expands store source target) : target.embed.shallow = source :=
  Proofs.Formats.Dasl.expands_shallow expanded

theorem Expands.bindings_subset {source : Shallow Name} {target : Named Name}
    (expanded : Expands store source target) : target.embed.bindings.Subset store :=
  Proofs.Formats.Dasl.expands_bindings expanded

theorem FullNames.toPartial {root : Name} {target : Named Name} (present : FullNames store root target) :
    PartialNames store root target.embed := by
  obtain ⟨source, hit, expanded⟩ := present
  exact ⟨expanded.shallow_eq.symm ▸ hit, expanded.bindings_subset⟩

theorem FullNames.mono {extended : Store Name} (incl : store.Subset extended)
    {root : Name} {target : Named Name} (present : FullNames store root target) :
    FullNames extended root target := by
  obtain ⟨source, hit, expanded⟩ := present
  exact ⟨source, incl.1 hit, Proofs.Formats.Dasl.expands_mono incl expanded⟩

theorem exists_full_of_accessible {root : Name} (accessible : Acc (Depends store) root)
    (present : ∃ source, store.objects root source) (closed : Closed store) :
    ∃ target, FullNames store root target :=
  Proofs.Formats.Dasl.exists_full_of_accessible accessible present closed

theorem full_exists_iff (bound : store.Binding) (root : Name) :
    (∃ target, FullNames store root target) ↔
      (∃ source, store.objects root source) ∧ Acc (Depends store) root ∧ ClosedBelow store root :=
  ⟨fun ⟨_, full⟩ => Proofs.Formats.Dasl.full_requirements bound full,
   fun ⟨present, accessible, closed⟩ => Proofs.Formats.Dasl.exists_full_below accessible present closed⟩

/-- A finite full expansion in a binding store rules out reachable object-reference cycles. -/
theorem FullNames.accessible (bound : store.Binding) {root : Name} {target : Named Name}
    (full : FullNames store root target) : Acc (Depends store) root :=
  Proofs.Formats.Dasl.full_accessible bound full

/-- Complete in a supplied binding extension, without dropping any old bindings. The
extension must be justified separately by any wire validity and hash policy. -/
theorem completion_in_extension {base : Store Name} {root : Name} (preserves : base.Subset store)
    (bound : store.Binding) (accessible : Acc (Depends store) root)
    (present : ∃ source, store.objects root source) (closed : Closed store) :
    base.Subset store ∧ ∃ target, FullNames store root target ∧
      ∀ other, FullNames store root other → other = target := by
  obtain ⟨target, expands⟩ := exists_full_of_accessible accessible present closed
  exact ⟨preserves, target, expands, fun _ other => fullNames_binding bound other expands⟩

/-- A logical, not executable, lookup for finite full expansions. -/
noncomputable def fullLookup (bound : store.Binding) : Name → Option (Named Name) :=
  (fullNames_binding bound).lookup

@[simp] theorem fullLookup_eq_some (bound : store.Binding) {name : Name} {value : Named Name} :
    fullLookup bound name = some value ↔ FullNames store name value :=
  (fullNames_binding bound).lookup_eq_some

end Silmaril.Formats.Dasl
