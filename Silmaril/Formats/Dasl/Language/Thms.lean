module

public import Silmaril.Formats.Dasl.Language.Defs
public import Silmaril.Semantics.Naming.Observations.Thms
import Silmaril.Formats.Dasl.Thms
import Silmaril.Proofs.Formats.Dasl.Language

public section

namespace Silmaril.Formats.Dasl

open Silmaril.Semantics.Naming

variable {Name : Type} {store extended : Store Name}

theorem PartialNames.mono (incl : store.Subset extended) {root : Name} {tree : Partial Name}
    (hit : PartialNames store root tree) : PartialNames extended root tree :=
  ⟨incl.1 hit.1, hit.2.trans incl⟩

theorem PartialNames.of_extends {root : Name} {seed tree : Partial Name}
    (hit : PartialNames store root tree) (step : Extends seed tree) : PartialNames store root seed :=
  ⟨step.shallow_eq.symm ▸ hit.1, step.bindings_subset.trans hit.2⟩

theorem PartialNames.shallow {root : Name} {source : Shallow Name} (hit : store.objects root source) :
    PartialNames store root source.embed := Proofs.Formats.Dasl.Language.partialNames_shallow hit

namespace PartialLanguage

variable {language : PartialLanguage Name}

theorem witness_subset_iff {root : Name} {tree : Partial Name} :
    (witness root tree).Subset store ↔ PartialNames store root tree :=
  Proofs.Formats.Dasl.Language.witness_subset_iff

/-- `observed` itself satisfies the language and is included in every satisfying relation. -/
theorem observed_subset_iff : language.observed.Subset store ↔ language.Satisfies store :=
  Proofs.Formats.Dasl.Language.observed_subset_iff

theorem satisfies_observed (language : PartialLanguage Name) : language.Satisfies language.observed :=
  Proofs.Formats.Dasl.Language.satisfies_observed language

theorem binding_iff_satisfiable : language.observed.Binding ↔ ∃ ambient, ambient.Binding ∧ language.Satisfies ambient :=
  ⟨fun bound => ⟨language.observed, bound, language.satisfies_observed⟩,
    fun ⟨_, bound, satisfies⟩ => bound.subset (observed_subset_iff.mpr satisfies)⟩

theorem realize_satisfies (roots : Relation Name (Shallow Name)) (store : Store Name) :
    (realize roots store).Satisfies store := fun _ _ hit => hit.2

theorem realize_observed_subset (roots : Relation Name (Shallow Name)) (store : Store Name) :
    (realize roots store).observed.Subset store := observed_subset_iff.mpr (realize_satisfies roots store)

theorem realize_binding (roots : Relation Name (Shallow Name)) (bound : store.Binding) :
    (realize roots store).observed.Binding := bound.subset (realize_observed_subset roots store)

theorem realize_saturatedIn (roots : Relation Name (Shallow Name)) (store : Store Name) :
    (realize roots store).SaturatedIn store :=
  fun _ _ _ member step included => ⟨step.shallow_eq ▸ member.1, included⟩

theorem realize_saturated (roots : Relation Name (Shallow Name)) (store : Store Name) :
    (realize roots store).Saturated := fun _ _ _ hit step included =>
  realize_saturatedIn roots store hit step (included.mono (realize_observed_subset roots store))

theorem realize_shallowRoots {roots : Relation Name (Shallow Name)} (covered : Subset roots store.objects) :
    (realize roots store).shallowRoots = roots := Proofs.Formats.Dasl.Language.realize_shallowRoots covered

/-- Recover the entire store only when every binding is actually witnessed. -/
theorem realize_observed_eq_iff (roots : Relation Name (Shallow Name)) (store : Store Name) :
    (realize roots store).observed = store ↔ store.Subset (realize roots store).observed :=
  Proofs.Formats.Dasl.Language.realize_observed_eq_iff roots store

theorem realize_observed_iff : realize language.shallowRoots language.observed = language ↔
    language.HasShallowSeeds ∧ language.Saturated := Proofs.Formats.Dasl.Language.realize_observed_iff

variable {external : Store Name} {compatible : language.observed.MergeCompatible external}

theorem subset_expand : Subset language (language.expand external compatible) :=
  fun _ tree hit => ⟨tree, hit, .same tree,
    (language.satisfies_observed hit).mono (Stores.subset_union_left _ _)⟩

theorem observed_subset_expand : language.observed.Subset (language.expand external compatible).observed :=
  Stores.collect_mono subset_expand witness

theorem expand_shallowRoots : (language.expand external compatible).shallowRoots = language.shallowRoots :=
  Proofs.Formats.Dasl.Language.expand_shallowRoots

theorem expand_roots : (language.expand external compatible).roots = language.roots :=
  Proofs.Formats.Dasl.Language.expand_roots

theorem expand_observed_subset : (language.expand external compatible).observed.Subset (language.observed.union external) :=
  observed_subset_iff.mpr fun _ _ ⟨_, _, _, included⟩ => included

theorem expand_binding : (language.expand external compatible).observed.Binding :=
  Stores.Binding.subset compatible (expand_observed_subset (compatible := compatible))

/-- Use this stronger inclusion to assert external satisfaction, not joint binding alone. -/
theorem expand_satisfies_external (incl : language.observed.Subset external) :
    (language.expand external compatible).Satisfies external :=
  observed_subset_iff.mp (expand_observed_subset.trans (Stores.union_subset incl (Stores.Subset.refl _)))

theorem expand_satisfies_external_iff : (language.expand external compatible).Satisfies external ↔
    language.observed.Subset external :=
  ⟨fun satisfied => observed_subset_expand.trans (observed_subset_iff.mpr satisfied), expand_satisfies_external⟩

theorem expand_saturatedIn : (language.expand external compatible).SaturatedIn (language.observed.union external) :=
  fun _ _ _ ⟨start, hit, first, _⟩ second included => ⟨start, hit, first.trans second, included⟩

theorem expand_saturated : (language.expand external compatible).Saturated :=
  fun _ _ _ member step included => expand_saturatedIn member step (included.mono expand_observed_subset)

theorem expand_realize (seeds : language.HasShallowSeeds) : language.expand external compatible =
    realize language.shallowRoots (language.observed.union external) := Proofs.Formats.Dasl.Language.expand_realize seeds

end PartialLanguage

theorem recognized_mono (incl : store.Subset extended) (predicate : Value → Prop) :
    Recognized store predicate ⊆ Recognized extended predicate := Proofs.Formats.Dasl.Language.recognized_mono incl predicate

theorem partialRecognized_mono (incl : store.Subset extended) (predicate : Partial Name → Prop) :
    PartialRecognized store predicate ⊆ PartialRecognized extended predicate :=
  fun _ ⟨tree, hit, accepts⟩ => ⟨tree, hit.mono incl, accepts⟩

end Silmaril.Formats.Dasl
