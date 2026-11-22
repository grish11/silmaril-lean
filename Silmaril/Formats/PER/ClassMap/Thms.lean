module

public import Silmaril.Formats.PER.ClassMap.Defs
import Silmaril.Proofs.Formats.PER.ClassMap

public section

namespace Silmaril.Formats.PER.ClassMap

open Silmaril.Proofs.Formats

variable {Key Class Other : Type}

theorem intrinsic_hit (relation : PER Key) {key : Key} (hit : relation.Dom key) :
    intrinsic relation key = some (_root_.Quotient.mk _ ⟨key, hit⟩) := PERClassMap.intrinsic_hit relation hit

theorem intrinsic_miss (relation : PER Key) {key : Key} (miss : ¬ relation.Dom key) :
    intrinsic relation key = none := PERClassMap.intrinsic_miss relation miss

theorem intrinsic_fibers (relation : PER Key) : fibers (intrinsic relation) = relation :=
  PERClassMap.intrinsic_fibers relation

theorem extensional_hit (relation : PER Key) {key : Key} (hit : relation.Dom key) :
    extensional relation key = some (relation.classOf key) := PERClassMap.extensional_hit relation hit

theorem extensional_fibers (relation : PER Key) : fibers (extensional relation) = relation :=
  PERClassMap.extensional_fibers relation

theorem extensional_range (relation : PER Key) (group : Set Key) :
    (∃ key, extensional relation key = some group) ↔ group ∈ relation.classes := PERClassMap.extensional_range relation group

theorem coherent_iff (lookup : ClassMap Key (Set Key)) :
    Coherent lookup ↔ lookup = extensional (fibers lookup) := PERClassMap.coherent_iff lookup

theorem extensional_coherent (relation : PER Key) : Coherent (extensional relation) :=
  (coherent_iff _).mpr (congrArg extensional (extensional_fibers relation).symm)

theorem Coherent.mem_assigned {lookup : ClassMap Key (Set Key)} (valid : Coherent lookup) {key : Key}
    {group : Set Key} (hit : lookup key = some group) : key ∈ group := (valid hit).symm ▸ hit

/-- The intrinsic classes are exactly the labels observed in any map that
represents this PER. Unused labels do not affect the equivalence. -/
noncomputable def quotientEquiv (lookup : ClassMap Key Class) {relation : PER Key}
    (represents : fibers lookup = relation) : relation.Quotient ≃ Used lookup :=
  PERClassMap.quotientEquiv lookup represents

theorem quotientEquiv_recovers (lookup : ClassMap Key Class) {relation : PER Key}
    (represents : fibers lookup = relation) (key : Key) :
    (intrinsic relation key).map (fun group => (quotientEquiv lookup represents group).val) = lookup key :=
  PERClassMap.quotientEquiv_recovers lookup represents key

theorem usedLookup_value (lookup : ClassMap Key Class) (key : Key) :
    (usedLookup lookup key).map Subtype.val = lookup key := PERClassMap.usedLookup_value lookup key

noncomputable def relabel (lookup : ClassMap Key Class) (other : ClassMap Key Other)
    (same : fibers lookup = fibers other) : Used lookup ≃ Used other := PERClassMap.relabel lookup other same

theorem relabel_recovers (lookup : ClassMap Key Class) (other : ClassMap Key Other)
    (same : fibers lookup = fibers other) (key : Key) :
    (usedLookup lookup key).map (relabel lookup other same) = usedLookup other key :=
  PERClassMap.relabel_recovers lookup other same key

theorem relabel_unique (lookup : ClassMap Key Class) (other : ClassMap Key Other)
    (same : fibers lookup = fibers other) (rename : Used lookup ≃ Used other)
    (recovers : ∀ key, (usedLookup lookup key).map rename = usedLookup other key) :
    rename = relabel lookup other same := PERClassMap.relabel_unique lookup other same rename recovers

theorem fibers_used (lookup : ClassMap Key Class) : fibers (usedLookup lookup) = fibers lookup := by
  rw [← fibers_relabel (usedLookup lookup) Subtype.val Subtype.val_injective]
  exact congrArg fibers (funext (usedLookup_value lookup))

theorem fibers_eq_of_relabel {lookup : ClassMap Key Class} {other : ClassMap Key Other} (rename : Used lookup ≃ Used other)
    (recovers : ∀ key, (usedLookup lookup key).map rename = usedLookup other key) : fibers lookup = fibers other := by
  rw [← fibers_used lookup, ← fibers_used other, ← fibers_relabel _ rename rename.injective]
  exact congrArg fibers (funext recovers)

theorem fibers_eq_iff_relabel (lookup : ClassMap Key Class) (other : ClassMap Key Other) :
    fibers lookup = fibers other ↔ ∃ rename : Used lookup ≃ Used other,
      ∀ key, (usedLookup lookup key).map rename = usedLookup other key :=
  ⟨fun same => ⟨relabel lookup other same, relabel_recovers lookup other same⟩,
    fun ⟨rename, recovers⟩ => fibers_eq_of_relabel rename recovers⟩

theorem representatives_fibers {relation : PER Key} {pick : relation.Quotient → Key} (member : Selects relation pick) :
    fibers (representatives relation pick) = relation :=
  (fibers_relabel (intrinsic relation) pick (PERClassMap.selector_injective member)).trans (intrinsic_fibers relation)

/-- Only a selector with the membership law yields fixed representative
labels. No assertion about the reachability of an arbitrary parent map. -/
theorem representative_fixed {relation : PER Key} {pick : relation.Quotient → Key} (member : Selects relation pick)
    {key root : Key} (hit : representatives relation pick key = some root) :
    representatives relation pick root = some root := PERClassMap.selector_rooted member hit

theorem canonical_selects {relation : PER Key} (policy : relation.Canonical) : Selects relation (canonicalSelector policy) :=
  policy.normalize_related

theorem canonical_unique {relation : PER Key} (policy : relation.Canonical) {pick : relation.Quotient → Key}
    (member : Selects relation pick) (selected : ∀ group, policy.selected (pick group)) :
    pick = canonicalSelector policy := PERClassMap.canonical_unique policy member selected

end Silmaril.Formats.PER.ClassMap
