module

public import Silmaril.Formats.PER.ClassMap.Defs

public section

namespace Silmaril.Proofs.Formats.PERClassMap

open Silmaril.Formats PER ClassMap

variable {Key Class Other : Type}

theorem intrinsic_hit (relation : PER Key) {key : Key} (hit : relation.Dom key) :
    intrinsic relation key = some (_root_.Quotient.mk _ ⟨key, hit⟩) := by
  simp [intrinsic, hit]

theorem intrinsic_miss (relation : PER Key) {key : Key} (miss : ¬ relation.Dom key) :
    intrinsic relation key = none := by simp [intrinsic, miss]

theorem extensional_hit (relation : PER Key) {key : Key} (hit : relation.Dom key) :
    extensional relation key = some (relation.classOf key) := by simp [extensional, hit]

theorem extensional_miss (relation : PER Key) {key : Key} (miss : ¬ relation.Dom key) :
    extensional relation key = none := by simp [extensional, miss]

theorem extensional_range (relation : PER Key) (group : Set Key) :
    (∃ key, extensional relation key = some group) ↔ group ∈ relation.classes := by
  constructor
  · rintro ⟨key, hit⟩
    classical
    by_cases known : relation.Dom key
    · exact ⟨key, known, Option.some.inj ((extensional_hit relation known).symm.trans hit)⟩
    · simp [extensional_miss relation known] at hit
  · rintro ⟨key, known, rfl⟩
    exact ⟨key, extensional_hit relation known⟩

theorem intrinsic_fibers (relation : PER Key) : fibers (intrinsic relation) = relation := by
  apply PER.ext
  intro left right
  constructor
  · intro edge
    obtain ⟨label, hl, hr⟩ := edge
    classical
    by_cases leftOk : relation.Dom left
    · by_cases rightOk : relation.Dom right
      · rw [intrinsic_hit relation leftOk] at hl
        rw [intrinsic_hit relation rightOk] at hr
        exact _root_.Quotient.exact (Option.some.inj (hl.trans hr.symm))
      · simp [intrinsic_miss relation rightOk] at hr
    · simp [intrinsic_miss relation leftOk] at hl
  · intro edge
    exact ⟨_, intrinsic_hit relation (relation.dom_left edge),
      (intrinsic_hit relation (relation.dom_right edge)).trans (congrArg some (_root_.Quotient.sound (relation.laws.symm edge)))⟩

theorem classOf_eq {relation : PER Key} {left right : Key} (present : relation.Dom left) :
    relation.classOf left = relation.classOf right ↔ relation.rel left right := by
  constructor
  · intro equal
    exact relation.laws.symm (show left ∈ relation.classOf right from equal ▸ present)
  · intro edge
    exact Set.ext fun _ => ⟨relation.laws.trans (relation.laws.symm edge), relation.laws.trans edge⟩

theorem extensional_fibers (relation : PER Key) : fibers (extensional relation) = relation := by
  apply PER.ext
  intro left right
  constructor
  · rintro ⟨group, hl, hr⟩
    classical
    by_cases leftOk : relation.Dom left
    · by_cases rightOk : relation.Dom right
      · rw [extensional_hit relation leftOk] at hl
        rw [extensional_hit relation rightOk] at hr
        exact (classOf_eq leftOk).mp (Option.some.inj (hl.trans hr.symm))
      · simp [extensional_miss relation rightOk] at hr
    · simp [extensional_miss relation leftOk] at hl
  · intro edge
    exact ⟨_, extensional_hit relation (relation.dom_left edge),
      (extensional_hit relation (relation.dom_right edge)).trans
        (congrArg some ((classOf_eq (relation.dom_left edge)).mpr edge).symm)⟩

theorem coherent_iff (lookup : ClassMap Key (Set Key)) :
    Coherent lookup ↔ lookup = extensional (fibers lookup) := by
  constructor
  · intro valid
    funext key
    cases hit : lookup key with
    | none => exact (extensional_miss _ (fun known => by simp [hit] at known)).symm
    | some group =>
      rw [extensional_hit _ ((fibers_dom lookup key).mpr (hit ▸ rfl))]
      exact congrArg some ((valid hit).trans (fibers_class lookup hit).symm)
  · intro same key group hit
    have known : (fibers lookup).Dom key := (fibers_dom lookup key).mpr (hit ▸ rfl)
    have actual : extensional (fibers lookup) key = some group := (congrFun same key).symm.trans hit
    exact (Option.some.inj (actual.symm.trans (extensional_hit _ known))).trans (fibers_class lookup hit)

def supportLabel (lookup : ClassMap Key Class) {relation : PER Key} (represents : fibers lookup = relation)
    (key : {key // relation.Dom key}) : Used lookup :=
  let known := (fibers_dom lookup key.val).mp (represents.symm ▸ key.property)
  ⟨(lookup key.val).get known, key.val, (Option.some_get known).symm⟩

theorem supportLabel_hit (lookup : ClassMap Key Class) {relation : PER Key} (represents : fibers lookup = relation)
    (key : {key // relation.Dom key}) : lookup key.val = some (supportLabel lookup represents key).val :=
  (Option.some_get _).symm

def quotientLabel (lookup : ClassMap Key Class) {relation : PER Key} (represents : fibers lookup = relation) :
    relation.Quotient → Used lookup :=
  _root_.Quotient.lift (supportLabel lookup represents) fun left right edge => by
    apply Subtype.ext
    obtain ⟨label, hl, hr⟩ := (represents.symm ▸ edge : (fibers lookup).rel left.val right.val)
    exact Option.some.inj ((supportLabel_hit lookup represents left).symm.trans
      (hl.trans (hr.symm.trans (supportLabel_hit lookup represents right))))

theorem quotientLabel_bijective (lookup : ClassMap Key Class) {relation : PER Key} (represents : fibers lookup = relation) :
    Function.Bijective (quotientLabel lookup represents) := by
  constructor
  · intro first second
    induction first using _root_.Quotient.inductionOn with
    | _ left =>
      induction second using _root_.Quotient.inductionOn with
      | _ right =>
        intro same
        have leftHit := supportLabel_hit lookup represents left
        have rightHit := supportLabel_hit lookup represents right
        have equal : (supportLabel lookup represents left).val = (supportLabel lookup represents right).val :=
          congrArg Subtype.val same
        exact _root_.Quotient.sound (represents ▸ (⟨_, leftHit, rightHit.trans (congrArg some equal.symm)⟩ :
          (fibers lookup).rel left.val right.val))
  · rintro ⟨label, key, hit⟩
    have known : relation.Dom key := represents ▸ (fibers_dom lookup key).mpr (hit ▸ rfl)
    refine ⟨_root_.Quotient.mk _ ⟨key, known⟩, Subtype.ext ?_⟩
    exact Option.some.inj ((supportLabel_hit lookup represents ⟨key, known⟩).symm.trans hit)

noncomputable def quotientEquiv (lookup : ClassMap Key Class) {relation : PER Key}
    (represents : fibers lookup = relation) : relation.Quotient ≃ Used lookup :=
  Equiv.ofBijective (quotientLabel lookup represents) (quotientLabel_bijective lookup represents)

theorem quotientEquiv_on_hit (lookup : ClassMap Key Class) {relation : PER Key}
    (represents : fibers lookup = relation) {key : Key} {label : Class} (hit : lookup key = some label)
    (known : relation.Dom key) :
    quotientEquiv lookup represents (_root_.Quotient.mk _ ⟨key, known⟩) = ⟨label, key, hit⟩ :=
  Subtype.ext (Option.some.inj ((supportLabel_hit lookup represents ⟨key, known⟩).symm.trans hit))

theorem quotientEquiv_recovers (lookup : ClassMap Key Class) {relation : PER Key}
    (represents : fibers lookup = relation) (key : Key) :
    (intrinsic relation key).map (fun group => (quotientEquiv lookup represents group).val) = lookup key := by
  cases hit : lookup key with
  | none =>
    have noSupport : ¬ relation.Dom key := fun known => by
      have present := (fibers_dom lookup key).mp (represents.symm ▸ known)
      simp [hit] at present
    simp [intrinsic_miss relation noSupport]
  | some label =>
    have known : relation.Dom key := represents ▸ (fibers_dom lookup key).mpr (hit ▸ rfl)
    simp [intrinsic_hit relation known, quotientEquiv_on_hit lookup represents hit known]

theorem usedLookup_hit (lookup : ClassMap Key Class) {key : Key} {label : Class} (hit : lookup key = some label) :
    usedLookup lookup key = some ⟨label, key, hit⟩ := by
  simp [usedLookup, Option.pbind_some' hit]

theorem usedLookup_miss (lookup : ClassMap Key Class) {key : Key} (miss : lookup key = none) :
    usedLookup lookup key = none := by simp [usedLookup, Option.pbind_none' miss]

theorem usedLookup_value (lookup : ClassMap Key Class) (key : Key) :
    (usedLookup lookup key).map Subtype.val = lookup key := by
  cases hit : lookup key with
  | none => rw [usedLookup_miss lookup hit]; rfl
  | some _ => rw [usedLookup_hit lookup hit]; rfl

noncomputable def relabel (lookup : ClassMap Key Class) (other : ClassMap Key Other)
    (same : fibers lookup = fibers other) : Used lookup ≃ Used other :=
  (quotientEquiv lookup rfl).symm.trans (quotientEquiv other same.symm)

theorem relabel_recovers (lookup : ClassMap Key Class) (other : ClassMap Key Other)
    (same : fibers lookup = fibers other) (key : Key) :
    (usedLookup lookup key).map (relabel lookup other same) = usedLookup other key := by
  cases hit : lookup key with
  | none =>
    have miss : other key = none := by
      cases present : other key with
      | none => rfl
      | some _ =>
        have known : (fibers lookup).Dom key := same.symm ▸ (fibers_dom other key).mpr (present ▸ rfl)
        simp [hit] at known
    rw [usedLookup_miss lookup hit, usedLookup_miss other miss]
    rfl
  | some value =>
    have known : (fibers lookup).Dom key := (fibers_dom lookup key).mpr (hit ▸ rfl)
    have present := (fibers_dom other key).mp (same ▸ known)
    obtain ⟨label, found⟩ := Option.isSome_iff_exists.mp present
    rw [usedLookup_hit lookup hit, usedLookup_hit other found]
    change some (relabel lookup other same ⟨value, key, hit⟩) = some ⟨label, key, found⟩
    rw [← quotientEquiv_on_hit lookup rfl hit known]
    simpa [relabel] using congrArg some (quotientEquiv_on_hit other same.symm found known)

theorem relabel_unique (lookup : ClassMap Key Class) (other : ClassMap Key Other)
    (same : fibers lookup = fibers other) (rename : Used lookup ≃ Used other)
    (recovers : ∀ key, (usedLookup lookup key).map rename = usedLookup other key) :
    rename = relabel lookup other same := by
  apply Equiv.ext
  rintro ⟨label, key, hit⟩
  have left := recovers key
  have right := relabel_recovers lookup other same key
  rw [usedLookup_hit lookup hit] at left right
  exact Option.some.inj (left.trans right.symm)

theorem selector_injective {relation : PER Key} {pick : relation.Quotient → Key} (member : Selects relation pick) :
    Function.Injective pick := by
  intro first second
  induction first using _root_.Quotient.inductionOn with
  | _ left =>
    induction second using _root_.Quotient.inductionOn with
    | _ right =>
      intro same
      exact _root_.Quotient.sound (relation.laws.trans (member left) (relation.laws.symm (same ▸ member right)))

theorem selector_rooted {relation : PER Key} {pick : relation.Quotient → Key} (member : Selects relation pick)
    {key root : Key} (hit : representatives relation pick key = some root) :
    representatives relation pick root = some root := by
  classical
  by_cases known : relation.Dom key
  · have identified : pick (_root_.Quotient.mk _ ⟨key, known⟩) = root := by
      simpa [representatives, intrinsic_hit relation known] using hit
    have edge : relation.rel key root := identified ▸ member ⟨key, known⟩
    have same : (_root_.Quotient.mk _ ⟨root, relation.dom_right edge⟩ : relation.Quotient) =
        _root_.Quotient.mk _ ⟨key, known⟩ := _root_.Quotient.sound (relation.laws.symm edge)
    simp [representatives, intrinsic_hit relation (relation.dom_right edge), same, identified]
  · simp [representatives, intrinsic_miss relation known] at hit

theorem canonical_unique {relation : PER Key} (policy : relation.Canonical) {pick : relation.Quotient → Key}
    (member : Selects relation pick) (selected : ∀ group, policy.selected (pick group)) :
    pick = canonicalSelector policy := by
  funext group
  induction group using _root_.Quotient.inductionOn with
  | _ key =>
    obtain ⟨root, _, unique⟩ := policy.representative key.val key.property
    exact (unique _ ⟨selected _, member key⟩).trans
      (unique _ ⟨(policy.normalize key).property, policy.normalize_related key⟩).symm

end Silmaril.Proofs.Formats.PERClassMap
