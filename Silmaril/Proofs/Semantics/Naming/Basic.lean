module

public import Silmaril.Semantics.Naming.Defs

public section

namespace Silmaril.Proofs.Semantics.Naming

open Silmaril.Semantics.Naming

theorem fillMissing_binding {Name Payload : Type} {base defaults : Relation Name Payload}
    (baseBound : Binding base) (defaultsBound : Binding defaults) : Binding (fillMissing base defaults) := by
  intro name left right first second
  rcases first with present | ⟨absent, supplied⟩ <;> rcases second with present' | ⟨absent', supplied'⟩
  · exact baseBound present present'
  · exact (absent' ⟨_, present⟩).elim
  · exact (absent ⟨_, present'⟩).elim
  · exact defaultsBound supplied supplied'

variable {Name Payload Wire : Type} {rel : Relation Name Payload}

theorem binding_iff_no_collisions : Binding rel ↔ collisions rel = ∅ := by
  classical
  constructor
  · intro bound
    ext name
    constructor
    · rintro ⟨_, _, left, right, different⟩
      exact (different (bound left right)).elim
    · exact False.elim
  · intro noCollisions name left right first second
    by_contra different
    have collision : name ∈ collisions rel := ⟨left, right, first, second, different⟩
    rw [noCollisions] at collision
    exact collision

theorem lookup_eq_some (bound : Binding rel) {name payload} :
    bound.lookup name = some payload ↔ rel name payload := by
  classical
  unfold Binding.lookup
  split
  · rename_i existsPayload
    have found := Classical.choose_spec existsPayload
    exact ⟨fun eq => Option.some.inj eq ▸ found, fun hit => congrArg some (bound found hit)⟩
  · rename_i absent
    exact ⟨(fun eq => by cases eq), fun hit => (absent ⟨payload, hit⟩).elim⟩

theorem lookup_project (bound : Binding rel) (decode : Payload → Option Wire) (name : Name) :
    ∀ projected : Binding (project rel decode),
      projected.lookup name = (bound.lookup name).bind decode := by
  intro projected
  apply Option.ext
  intro value
  rw [lookup_eq_some, Option.bind_eq_some_iff]
  exact exists_congr fun _ => and_congr (lookup_eq_some bound).symm Iff.rfl

theorem mem_names_quotient {equiv : Setoid Payload} {name : Name} {repr : Payload} :
    name ∈ names (quotient rel equiv) (Quotient.mk equiv repr) ↔
      ∃ otherRepr, name ∈ names rel otherRepr ∧ equiv.r otherRepr repr := by
  constructor
  · rintro ⟨otherRepr, hit, same⟩
    exact ⟨otherRepr, hit, Quotient.exact (Option.some.inj same)⟩
  · rintro ⟨otherRepr, hit, equivalent⟩
    exact ⟨otherRepr, hit, congrArg some (Quotient.sound equivalent)⟩

theorem project_uniqueNames (unique : UniqueNames rel) {decode : Payload → Option Wire}
    (canonical : ∀ ⦃firstName secondName left right value⦄,
      rel firstName left → rel secondName right →
      decode left = some value → decode right = some value → left = right) :
    UniqueNames (project rel decode) := by
  rintro value firstName secondName ⟨left, first, leftDecoded⟩ ⟨right, second, rightDecoded⟩
  have same := canonical first second leftDecoded rightDecoded
  exact unique first (same ▸ second)

theorem push_binding (bound : Binding rel) {serializes : Payload → Wire → Prop}
    (deterministic : Binding serializes) : Binding (push rel serializes) := by
  rintro name left right ⟨first, firstHit, firstWire⟩ ⟨second, secondHit, secondWire⟩
  exact deterministic firstWire (bound firstHit secondHit ▸ secondWire)

theorem push_parse_iff {serializes : Payload → Wire → Prop} {parse : Wire → Option Payload}
    (recovers : ∀ ⦃payload wire⦄, serializes payload wire → parse wire = some payload)
    {name wire payload} (parsed : parse wire = some payload) :
    push rel serializes name wire ↔ rel name payload ∧ serializes payload wire := by
  constructor
  · rintro ⟨source, hit, encoded⟩
    have same := Option.some.inj ((recovers encoded).symm.trans parsed)
    exact same ▸ ⟨hit, encoded⟩
  · rintro ⟨hit, encoded⟩
    exact ⟨payload, hit, encoded⟩

theorem flatten_binding {Obj : Type} {store : Stores Name Obj Wire} (bound : store.Binding)
    (disjoint : store.DisjointDomains) {serializes : Obj → Wire → Prop}
    (deterministic : Binding serializes) : Binding (store.flatten serializes) := by
  intro name left right first second
  rcases first with first | first <;> rcases second with second | second
  · exact push_binding bound.1 deterministic first second
  · obtain ⟨_, source, _⟩ := first
    exact (disjoint source second).elim
  · obtain ⟨_, source, _⟩ := second
    exact (disjoint source first).elim
  · exact bound.2 first second

theorem classify_merge (left right : Relation Name Payload) :
    Checked.merge (Checked.classify left) (Checked.classify right) = Checked.classify (union left right) := by
  classical
  by_cases leftBound : Binding left <;> by_cases rightBound : Binding right
  · simp [Checked.classify, Checked.merge, leftBound, rightBound]
  · have conflict : ¬ Binding (union left right) := by
      intro bound
      apply rightBound
      intro name firstPayload secondPayload first second
      exact bound (.inr first) (.inr second)
    simp [Checked.classify, Checked.merge, leftBound, rightBound, conflict]
  · have conflict : ¬ Binding (union left right) := by
      intro bound
      apply leftBound
      intro name firstPayload secondPayload first second
      exact bound (.inl first) (.inl second)
    simp [Checked.classify, Checked.merge, leftBound, rightBound, conflict]
  · have conflict : ¬ Binding (union left right) := by
      intro bound
      apply leftBound
      intro name firstPayload secondPayload first second
      exact bound (.inl first) (.inl second)
    simp [Checked.classify, Checked.merge, leftBound, rightBound, conflict]

theorem merge_assoc (left mid right : Checked Name Payload) :
    (left.merge mid).merge right = left.merge (mid.merge right) := by
  have absorb (snapshot : Checked Name Payload) : snapshot.merge .conflict = .conflict := by cases snapshot <;> rfl
  cases left <;> cases mid <;> cases right <;> try rfl
  case observed.observed.conflict => rw [absorb, absorb, absorb]
  case observed.observed.observed left leftBound mid midBound right rightBound =>
    have obs (rel : Relation Name Payload) (bound : Binding rel) :
        Checked.observed rel bound = Checked.classify rel := by simp [Checked.classify, bound]
    rw [obs left leftBound, obs mid midBound, obs right rightBound,
      classify_merge, classify_merge, classify_merge, classify_merge]
    congr 1
    funext name payload
    exact propext or_assoc

theorem merge_comm (left right : Checked Name Payload) : left.merge right = right.merge left := by
  cases left <;> cases right <;> try rfl
  case observed.observed left _ right _ =>
    change Checked.classify (union left right) = Checked.classify (union right left)
    congr 1
    funext name payload
    exact propext or_comm

theorem merge_idem (snapshot : Checked Name Payload) : snapshot.merge snapshot = snapshot := by
  cases snapshot with
  | conflict => rfl
  | observed rel bound =>
    have same : union rel rel = rel := by funext name payload; exact or_self (rel name payload)
    change Checked.classify (union rel rel) = _
    simp [same, Checked.classify, bound]

end Silmaril.Proofs.Semantics.Naming
