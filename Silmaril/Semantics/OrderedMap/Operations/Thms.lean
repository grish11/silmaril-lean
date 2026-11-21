module

public import Silmaril.Semantics.OrderedMap.Operations.Defs
import Silmaril.Proofs.Semantics.OrderedMap.Operations

public section

namespace Silmaril.Semantics.OrderedMap

section Finite

variable {Key Payload Error : Type} [LinearOrder Key]

theorem mem_domain (map : OrderedMap Key Payload) (key : Key) :
    key ∈ map.domain ↔ (map.lookup? key).isSome :=
  Proofs.Semantics.OrderedMap.Operations.mem_domain map key

theorem cardinality_eq (map : OrderedMap Key Payload) : map.cardinality = map.domain.card :=
  Proofs.Semantics.OrderedMap.Operations.cardinality_eq map

theorem domainSubset_spec (left right : OrderedMap Key Payload) :
    left.domainSubset right = true ↔ left.domain ⊆ right.domain := by simp [domainSubset]

theorem submap_spec [DecidableEq Payload] (left right : OrderedMap Key Payload) :
    left.submap right = true ↔ ∀ key value, left.lookup? key = some value → right.lookup? key = some value :=
  Proofs.Semantics.OrderedMap.Operations.submap_spec left right

/-- Carrier recovery: a returned finite map has exactly the pointwise results;
if those results describe a finite map, evaluation recovers it. -/
theorem combine_spec (kind : Combine) (overlap : Overlap Key Payload Error) (left right result : OrderedMap Key Payload) :
    left.combine kind overlap right = .ok result ↔
      ∀ key, kind.atKey overlap key (left.lookup? key) (right.lookup? key) = .ok (result.lookup? key) :=
  Proofs.Semantics.OrderedMap.Operations.combine_spec kind overlap left right result

theorem combine_succeeds_iff (kind : Combine) (overlap : Overlap Key Payload Error) (left right : OrderedMap Key Payload) :
    (∃ result, left.combine kind overlap right = .ok result) ↔
      ∀ key leftValue rightValue, left.lookup? key = some leftValue → right.lookup? key = some rightValue →
        ∃ value, overlap key leftValue rightValue = .ok value :=
  Proofs.Semantics.OrderedMap.Operations.combine_succeeds_iff kind overlap left right

theorem combine_reject_succeeds_iff (kind : Combine) (left right : OrderedMap Key Payload) :
    (∃ result, left.combine kind Overlap.reject right = .ok result) ↔ Disjoint left.domain right.domain :=
  Proofs.Semantics.OrderedMap.Operations.combine_reject_succeeds_iff kind left right

end Finite

namespace Combine

variable {Key Payload Error : Type}
variable (key : Key) (left right : Option Payload)

theorem union_keepLeft : union.atKey (Overlap.keepLeft (Error := Error)) key left right =
    .ok (left.orElse fun _ => right) := by cases left <;> cases right <;> rfl

theorem union_keepRight : union.atKey (Overlap.keepRight (Error := Error)) key left right =
    .ok (right.orElse fun _ => left) := by cases left <;> cases right <;> rfl

theorem intersection_keepLeft : intersection.atKey (Overlap.keepLeft (Error := Error)) key left right =
    .ok (if right.isSome then left else none) := by cases left <;> cases right <;> rfl

theorem intersection_keepRight : intersection.atKey (Overlap.keepRight (Error := Error)) key left right =
    .ok (if left.isSome then right else none) := by cases left <;> cases right <;> rfl

theorem union_discard : union.atKey (Overlap.discard (Error := Error)) key left right =
    .ok (if left.isSome = right.isSome then none else left.orElse fun _ => right) := by
  cases left <;> cases right <;> rfl

theorem intersection_discard : intersection.atKey (Overlap.discard (Error := Error)) key left right = .ok none := by
  cases left <;> cases right <;> rfl

theorem reject (kind : Combine) : kind.atKey Overlap.reject key left right =
    if left.isSome && right.isSome then .error key else kind.atKey Overlap.discard key left right := by
  cases kind <;> cases left <;> cases right <;> rfl

end Combine

end Silmaril.Semantics.OrderedMap

namespace Silmaril.Semantics.OrderedSet

variable {Key Error : Type} [LinearOrder Key]

theorem contains_spec (set : OrderedSet Key) (key : Key) :
    set.contains key = true ↔ key ∈ set.domain := (set.mem_domain key).symm

theorem combine_membership (kind : OrderedMap.Combine) (overlap : OrderedMap.Overlap Key Unit Error)
    (left right result : OrderedSet Key) (ok : left.combine kind overlap right = .ok result) (key : Key) :
    kind.atKey overlap key (if left.contains key then some () else none) (if right.contains key then some () else none) =
      .ok (if result.contains key then some () else none) :=
  Proofs.Semantics.OrderedMap.Operations.combine_membership kind overlap left right result ok key

end Silmaril.Semantics.OrderedSet
