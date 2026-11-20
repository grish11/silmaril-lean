module

public import Silmaril.Formats.Dasl.Language.Defs
public import Silmaril.Formats.Dasl.Resolve.Thms
public import Silmaril.Formats.Dasl.Thms
public import Silmaril.Semantics.Naming.Observations.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.Language

open Silmaril.Formats.Dasl Silmaril.Semantics.Naming

variable {Name : Type} {language : PartialLanguage Name} {store external : Store Name}

theorem witness_subset_iff {root : Name} {tree : Partial Name} :
    (PartialLanguage.witness root tree).Subset store ↔ PartialNames store root tree := by
  constructor
  · intro incl
    exact ⟨incl.1 (Or.inl ⟨rfl, rfl⟩), ⟨fun _ _ hit => incl.1 (Or.inr hit), incl.2⟩⟩
  · rintro ⟨rootHit, nested⟩
    refine ⟨?_, nested.2⟩
    rintro name source (⟨rfl, rfl⟩ | hit)
    · exact rootHit
    · exact nested.1 hit

theorem embed_bindings_subset (source : Shallow Name) : source.embed.bindings.Subset store := by
  induction source with
  | ref | i64 | bytes | string | bool | null =>
    exact ⟨fun _ _ hit => hit.elim, fun _ _ hit => hit.elim⟩
  | obj impossible _ _ | blob impossible _ => exact impossible.elim
  | dict _ _ ih | list _ _ ih =>
    refine ⟨?_, ?_⟩ <;> rintro name payload ⟨index, hit⟩
    · exact (ih index).1 hit
    · exact (ih index).2 hit

theorem partialNames_shallow {root : Name} {source : Shallow Name} (hit : store.objects root source) :
    PartialNames store root source.embed :=
  ⟨source.shallow_embed.symm ▸ hit, embed_bindings_subset source⟩

theorem observed_subset_iff : language.observed.Subset store ↔ language.Satisfies store :=
  Stores.collect_subset_iff.trans
    ⟨fun incl _ _ hit => witness_subset_iff.mp (incl hit),
      fun satisfied _ _ hit => witness_subset_iff.mpr (satisfied hit)⟩

theorem satisfies_observed (language : PartialLanguage Name) : language.Satisfies language.observed :=
  observed_subset_iff.mp (Stores.Subset.refl _)

theorem realize_shallowRoots {roots : Relation Name (Shallow Name)} (covered : Subset roots store.objects) :
    (PartialLanguage.realize roots store).shallowRoots = roots := by
  funext root source
  apply propext
  constructor
  · rintro ⟨tree, hit, same⟩
    exact same ▸ hit.1
  · intro hit
    exact ⟨source.embed, ⟨source.shallow_embed.symm ▸ hit, partialNames_shallow (covered hit)⟩,
      source.shallow_embed⟩

theorem realize_observed_eq_iff (roots : Relation Name (Shallow Name)) (store : Store Name) :
    (PartialLanguage.realize roots store).observed = store ↔
      store.Subset (PartialLanguage.realize roots store).observed := by
  constructor
  · intro same
    rw [same]
    exact Stores.Subset.refl store
  · intro covered
    have included : (PartialLanguage.realize roots store).observed.Subset store :=
      observed_subset_iff.mpr fun _ _ hit => hit.2
    exact Stores.Subset.antisymm included covered

theorem realize_observed_iff :
    PartialLanguage.realize language.shallowRoots language.observed = language ↔
      language.HasShallowSeeds ∧ language.Saturated := by
  constructor
  · intro reconstructed
    refine ⟨?_, ?_⟩
    · intro root tree hit
      rw [← reconstructed]
      exact ⟨⟨tree, hit, tree.shallow.shallow_embed.symm⟩,
        partialNames_shallow ((satisfies_observed language hit).1)⟩
    · intro root seed tree hit step included
      rw [← reconstructed]
      exact ⟨⟨seed, hit, step.shallow_eq⟩, included⟩
  · rintro ⟨seeds, saturated⟩
    funext root tree
    apply propext
    constructor
    · rintro ⟨⟨seed, hit, same⟩, included⟩
      exact saturated (seeds hit) (same.symm ▸ tree.shallow_le) included
    · intro hit
      exact ⟨⟨tree, hit, rfl⟩, satisfies_observed language hit⟩

theorem expand_realize {compatible : language.observed.MergeCompatible external}
    (seeds : language.HasShallowSeeds) :
    language.expand external compatible = PartialLanguage.realize language.shallowRoots (language.observed.union external) := by
  funext root tree
  apply propext
  constructor
  · rintro ⟨seed, hit, step, included⟩
    exact ⟨⟨seed, hit, step.shallow_eq⟩, included⟩
  · rintro ⟨⟨seed, hit, same⟩, included⟩
    exact ⟨seed.shallow.embed, seeds hit, same.symm ▸ tree.shallow_le, included⟩

theorem expand_shallowRoots {compatible : language.observed.MergeCompatible external} :
    (language.expand external compatible).shallowRoots = language.shallowRoots := by
  funext root source
  apply propext
  constructor
  · rintro ⟨_, ⟨seed, hit, step, _⟩, same⟩
    exact ⟨seed, hit, step.shallow_eq.trans same⟩
  · rintro ⟨tree, hit, same⟩
    have present := satisfies_observed language hit
    exact ⟨tree, ⟨tree, hit, .same tree, ⟨Or.inl present.1,
      present.2.trans (Stores.subset_union_left _ _)⟩⟩, same⟩

theorem expand_roots {compatible : language.observed.MergeCompatible external} :
    (language.expand external compatible).roots = language.roots := by
  apply Set.ext
  intro root
  constructor
  · rintro ⟨_, seed, hit, _, _⟩
    exact ⟨seed, hit⟩
  · rintro ⟨tree, hit⟩
    have present := satisfies_observed language hit
    exact ⟨tree, tree, hit, .same tree, ⟨Or.inl present.1,
      present.2.trans (Stores.subset_union_left _ _)⟩⟩

theorem recognized_mono {extended : Store Name} (incl : store.Subset extended) (predicate : Value → Prop) :
    Recognized store predicate ⊆ Recognized extended predicate := by
  rintro root ⟨value, ⟨target, hit, erased⟩, accepts⟩
  exact ⟨value, ⟨target, hit.mono incl, erased⟩, accepts⟩

end Silmaril.Proofs.Formats.Dasl.Language
