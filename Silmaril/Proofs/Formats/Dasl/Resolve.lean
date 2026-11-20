module

public import Silmaril.Formats.Dasl.Resolve.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl

open Silmaril.Formats.Dasl Silmaril.Semantics.Naming

variable {Name : Type} {store : Store Name}

theorem expands_unique (bound : store.Binding) {source : Shallow Name} {left right : Named Name}
    (first : Expands store source left) (second : Expands store source right) : left = right := by
  induction first generalizing right with
  | obj hit _ ih =>
    cases second with
    | obj other next => exact congrArg (Tree.obj _) (ih (bound.1 hit other ▸ next))
  | blob hit =>
    cases second with
    | blob other => exact congrArg (Tree.blob _) (bound.2 hit other)
  | dict _ ih =>
    cases second with
    | dict next => exact congrArg (Tree.dict _) (funext fun key => ih key (next key))
  | list _ ih =>
    cases second with
    | list next => exact congrArg (Tree.list _) (funext fun index => ih index (next index))
  | _ => cases second; rfl

theorem full_binding (bound : store.Binding) : Binding (FullNames store) := by
  rintro name left right ⟨_, hit, first⟩ ⟨_, other, second⟩
  exact expands_unique bound first (bound.1 hit other ▸ second)

theorem value_binding (bound : store.Binding) : Binding (ValueNames store) := by
  rintro name left right ⟨leftNamed, first, rfl⟩ ⟨rightNamed, second, rfl⟩
  exact congrArg Named.erase (full_binding bound first second)

theorem expands_shallow {source : Shallow Name} {target : Named Name}
    (expanded : Expands store source target) : (target.embed).shallow = source := by
  induction expanded with
  | dict _ ih => exact congrArg (Tree.dict _) (funext ih)
  | list _ ih => exact congrArg (Tree.list _) (funext ih)
  | _ => rfl

theorem expands_bindings {source : Shallow Name} {target : Named Name}
    (expanded : Expands store source target) : target.embed.bindings.Subset store := by
  induction expanded with
  | obj hit child ih =>
    refine ⟨?_, ih.2⟩
    intro name value witnessed
    rcases witnessed with ⟨rfl, view⟩ | deeper
    · exact (view.trans (expands_shallow child)).symm ▸ hit
    · exact ih.1 deeper
  | blob hit =>
    refine ⟨by intro name payload impossible; exact impossible.elim, ?_⟩
    rintro name payload ⟨rfl, rfl⟩
    exact hit
  | dict _ ih | list _ ih =>
    refine ⟨?_, ?_⟩ <;> rintro name value ⟨index, hit⟩
    · exact (ih index).1 hit
    · exact (ih index).2 hit
  | _ => exact ⟨by intro name payload impossible; exact impossible.elim,
                 by intro name payload impossible; exact impossible.elim⟩

theorem expands_mono {extended : Store Name} (incl : store.Subset extended)
    {source : Shallow Name} {target : Named Name} (expanded : Expands store source target) :
    Expands extended source target := by
  induction expanded with
  | obj hit _ ih => exact .obj (incl.1 hit) ih
  | blob hit => exact .blob (incl.2 hit)
  | dict _ ih => exact .dict ih
  | list _ ih => exact .list ih
  | _ => constructor

theorem expansion_of_links {source : Shallow Name}
    (objects : ∀ child, Link.obj child ∈ source.directLinks → ∃ value, FullNames store child value)
    (blobs : ∀ child, Link.blob child ∈ source.directLinks → ∃ payload, store.blobs child payload) :
    ∃ target, Expands store source target := by
  classical
  induction source with
  | ref link =>
    cases link with
    | obj name =>
      obtain ⟨target, _, hit, expanded⟩ := objects name rfl
      exact ⟨.obj name target, .obj hit expanded⟩
    | blob name =>
      obtain ⟨payload, hit⟩ := blobs name rfl
      exact ⟨.blob name payload, .blob hit⟩
  | obj impossible _ _ | blob impossible _ => exact impossible.elim
  | dict keys children ih =>
    have kids (key : ↥keys) := ih key (fun name hit => objects name ⟨key, hit⟩)
      (fun name hit => blobs name ⟨key, hit⟩)
    exact ⟨.dict keys (fun key => (kids key).choose), .dict (fun key => (kids key).choose_spec)⟩
  | list len children ih =>
    have kids (index : Fin len) := ih index (fun name hit => objects name ⟨index, hit⟩)
      (fun name hit => blobs name ⟨index, hit⟩)
    exact ⟨.list len (fun index => (kids index).choose), .list (fun index => (kids index).choose_spec)⟩
  | _ => exact ⟨_, by constructor⟩

theorem exists_full_of_accessible {root : Name} (accessible : Acc (Depends store) root)
    (present : ∃ source, store.objects root source) (closed : Closed store) :
    ∃ target, FullNames store root target := by
  induction accessible with
  | intro parent _ ih =>
    obtain ⟨source, hit⟩ := present
    have covered := closed hit
    obtain ⟨target, expanded⟩ := expansion_of_links
      (fun child linked => ih child ⟨source, hit, linked⟩ (covered.1 child linked)) covered.2
    exact ⟨target, source, hit, expanded⟩

theorem exists_full_below {root : Name} (accessible : Acc (Depends store) root)
    (present : ∃ source, store.objects root source) (closed : ClosedBelow store root) :
    ∃ target, FullNames store root target := by
  have descend {parent} (reachable : Reachable store root parent) (access : Acc (Depends store) parent)
      (hit : ∃ source, store.objects parent source) : ∃ target, FullNames store parent target := by
    induction access with
    | intro parent _ ih =>
      obtain ⟨source, read⟩ := hit
      have covered := closed reachable read
      obtain ⟨target, expanded⟩ := expansion_of_links (fun child linked => by
        have edge : Depends store child parent := ⟨source, read, linked⟩
        exact ih child edge (reachable.tail edge) (covered.1 child linked)) covered.2
      exact ⟨target, source, read, expanded⟩
  exact descend .refl accessible present

theorem expands_covers {source : Shallow Name} {target : Named Name}
    (expanded : Expands store source target) :
    (∀ child, Link.obj child ∈ source.directLinks → ∃ value, FullNames store child value) ∧
      (∀ child, Link.blob child ∈ source.directLinks → ∃ payload, store.blobs child payload) := by
  induction expanded with
  | obj read expanded _ =>
    refine ⟨fun _ linked => ?_, fun _ linked => by cases linked⟩
    cases linked
    exact ⟨_, _, read, expanded⟩
  | blob read =>
    constructor
    · intro _ linked; cases linked
    · intro _ linked; cases linked; exact ⟨_, read⟩
  | dict _ ih | list _ ih =>
    exact ⟨fun child ⟨index, hit⟩ => (ih index).1 child hit,
      fun child ⟨index, hit⟩ => (ih index).2 child hit⟩
  | _ => constructor <;> intro _ linked <;> cases linked

private theorem expanded_dependencies_accessible (bound : store.Binding)
    {source : Shallow Name} {target : Named Name} (expanded : Expands store source target) :
    ∀ name, Link.obj name ∈ source.directLinks → Acc (Depends store) name := by
  induction expanded with
  | @obj name source target hit _ ih =>
    intro child linked
    change Link.obj child = Link.obj name at linked
    cases linked
    refine Acc.intro _ ?_
    rintro descendant ⟨other, stored, edge⟩
    exact ih descendant (bound.1 stored hit ▸ edge)
  | blob => intro name linked; cases linked
  | dict _ ih | list _ ih =>
    rintro name ⟨index, linked⟩
    exact ih index name linked
  | _ => intro name linked; exact linked.elim

theorem full_accessible (bound : store.Binding) {root : Name} {target : Named Name}
    (full : FullNames store root target) : Acc (Depends store) root := by
  obtain ⟨source, hit, expanded⟩ := full
  refine Acc.intro _ ?_
  rintro name ⟨other, stored, edge⟩
  exact expanded_dependencies_accessible bound expanded name (bound.1 stored hit ▸ edge)

theorem full_requirements (bound : store.Binding) {root : Name} {target : Named Name}
    (full : FullNames store root target) :
    (∃ source, store.objects root source) ∧ Acc (Depends store) root ∧ ClosedBelow store root := by
  have accessible := full_accessible bound full
  obtain ⟨source, read, expanded⟩ := full
  refine ⟨⟨source, read⟩, accessible, ?_⟩
  have reachableFull {name} (reachable : Reachable store root name) : ∃ value, FullNames store name value := by
    induction reachable with
    | refl => exact ⟨target, source, read, expanded⟩
    | tail _ edge ih =>
      obtain ⟨_, _, hit, exp⟩ := ih
      obtain ⟨_, found, linked⟩ := edge
      exact (expands_covers exp).1 _ (bound.1 found hit ▸ linked)
  intro parent candidate reachable found
  obtain ⟨_, _, hit, exp⟩ := reachableFull reachable
  have covered := expands_covers exp
  cases bound.1 found hit
  exact ⟨fun child linked => by obtain ⟨_, source, hit, _⟩ := covered.1 child linked; exact ⟨source, hit⟩,
    covered.2⟩

end Silmaril.Proofs.Formats.Dasl
