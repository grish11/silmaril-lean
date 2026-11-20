module

public import Silmaril.Formats.Dasl.Resolve.Thms
public import Silmaril.Formats.Dasl.Resolve.Refinement.Defs
public import Silmaril.Formats.Dasl.Resolve.View.Thms
public import Silmaril.Formats.Dasl.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.Refinement

open Silmaril.Formats.Dasl

variable {Name : Type} {store : Store Name}

theorem extends_full (bound : store.Binding) {observed : Partial Name} {source : Shallow Name} {target : Named Name}
    (view : observed.shallow = source) (included : observed.bindings.Subset store) (expanded : Expands store source target) :
    Extends observed target.embed := by
  induction observed generalizing source target with
  | ref link =>
    subst source
    cases link <;> cases expanded <;> constructor
  | obj name child ih =>
    subst source
    cases expanded with
    | obj stored expanded =>
      apply Extends.obj
      exact ih (bound.1 (included.1 (Or.inl ⟨rfl, rfl⟩)) stored)
        ⟨fun _ _ hit => included.1 (Or.inr hit), included.2⟩ expanded
  | blob name payload =>
    subst source
    cases expanded with
    | blob stored =>
      cases bound.2 (included.2 ⟨rfl, rfl⟩) stored
      exact .same _
  | dict keys values ih =>
    subst source
    cases expanded with
    | dict expanded =>
      exact .dict fun key => ih key rfl
        ⟨fun _ _ hit => included.1 ⟨key, hit⟩, fun _ _ hit => included.2 ⟨key, hit⟩⟩ (expanded key)
  | list len values ih =>
    subst source
    cases expanded with
    | list expanded =>
      exact .list fun index => ih index rfl
        ⟨fun _ _ hit => included.1 ⟨index, hit⟩, fun _ _ hit => included.2 ⟨index, hit⟩⟩ (expanded index)
  | i64 | bytes | string | bool | null => subst source; cases expanded; exact .same _

private theorem readable_of_known {observed : Partial Name} (included : observed.bindings.Subset store)
    (known : observed.HasKnownBinding) : observed.shallow.HasReadableLink store := by
  induction observed with
  | obj name child ih => exact .inl ⟨name, Partial.shallow child, rfl, included.1 (Or.inl ⟨rfl, rfl⟩)⟩
  | blob name payload => exact .inr ⟨name, payload, rfl, included.2 ⟨rfl, rfl⟩⟩
  | dict _ children ih | list _ children ih =>
    have readable (index) (observed : Partial.HasKnownBinding (children index)) := ih index
      ⟨fun _ _ hit => included.1 ⟨index, hit⟩, fun _ _ hit => included.2 ⟨index, hit⟩⟩ observed
    have found : ∃ index, Partial.HasKnownBinding (children index) := by
      rcases known with ⟨name, payload, index, hit⟩ | ⟨name, payload, index, hit⟩
      · exact ⟨index, .inl ⟨name, payload, hit⟩⟩
      · exact ⟨index, .inr ⟨name, payload, hit⟩⟩
    obtain ⟨index, found⟩ := found
    rcases readable index found with ⟨name, value, link, stored⟩ | ⟨name, bytes, link, stored⟩
    · exact .inl ⟨name, value, ⟨index, link⟩, stored⟩
    · exact .inr ⟨name, bytes, ⟨index, link⟩, stored⟩
  | ref | i64 | bytes | string | bool | null =>
    rcases known with ⟨_, _, empty⟩ | ⟨_, _, empty⟩ <;> exact empty.elim

private theorem observe_readable (reader : Reader Name) {source : Shallow Name}
    (readable : source.HasReadableLink reader.store) : (reader.observe 1 source).HasKnownBinding := by
  induction source with
  | ref link =>
    rcases readable with ⟨name, value, direct, stored⟩ | ⟨name, bytes, direct, stored⟩
    · change Link.obj name = link at direct
      subst link
      change reader.object? name = some value at stored
      refine .inl ⟨name, value, ?_⟩
      simp only [Reader.observe, Shallow.observeWith, stored, Option.map_some, Partial.bindings]
      exact .inl ⟨trivial, value.shallow_embed.symm⟩
    · change Link.blob name = link at direct
      subst link
      change reader.blob? name = some bytes at stored
      exact .inr ⟨name, bytes, by simp [Reader.observe, Shallow.observeWith, stored, Partial.bindings]⟩
  | obj impossible _ _ | blob impossible _ => exact impossible.elim
  | dict _ children ih | list _ children ih =>
    have found : ∃ index, Shallow.HasReadableLink (children index) reader.store := by
      rcases readable with ⟨name, value, ⟨index, direct⟩, stored⟩ | ⟨name, bytes, ⟨index, direct⟩, stored⟩
      · exact ⟨index, .inl ⟨name, value, direct, stored⟩⟩
      · exact ⟨index, .inr ⟨name, bytes, direct, stored⟩⟩
    obtain ⟨index, found⟩ := found
    rcases ih index found with ⟨name, value, hit⟩ | ⟨name, bytes, hit⟩
    · exact .inl ⟨name, value, ⟨index, hit⟩⟩
    · exact .inr ⟨name, bytes, ⟨index, hit⟩⟩
  | i64 | bytes | string | bool | null =>
    rcases readable with ⟨_, _, empty, _⟩ | ⟨_, _, empty, _⟩ <;> exact empty.elim

theorem nontrivial_iff (bound : store.Binding) (root : Name) :
    (∃ observed, PartialNames store root observed ∧ observed.HasKnownBinding) ↔
      ∃ source, store.objects root source ∧ source.HasReadableLink store := by
  constructor
  · rintro ⟨observed, ⟨stored, included⟩, known⟩
    exact ⟨observed.shallow, stored, readable_of_known included known⟩
  · rintro ⟨source, stored, readable⟩
    let reader : Reader Name := ⟨bound.1.lookup, bound.2.lookup⟩
    have included : reader.store.Subset store :=
      ⟨fun _ _ hit => bound.1.lookup_eq_some.mp hit, fun _ _ hit => bound.2.lookup_eq_some.mp hit⟩
    have canRead : source.HasReadableLink reader.store := by
      rcases readable with ⟨name, value, direct, hit⟩ | ⟨name, bytes, direct, hit⟩
      · exact .inl ⟨name, value, direct, bound.1.lookup_eq_some.mpr hit⟩
      · exact .inr ⟨name, bytes, direct, bound.2.lookup_eq_some.mpr hit⟩
    refine ⟨reader.observe 1 source, ⟨(reader.observe_shallow 1 source).symm ▸ stored, ?_⟩,
      observe_readable reader canRead⟩
    have observed := reader.observe_bindings 1 source
    exact ⟨fun _ _ hit => included.1 (observed.1 hit), fun _ _ hit => included.2 (observed.2 hit)⟩

end Silmaril.Proofs.Formats.Dasl.Refinement
