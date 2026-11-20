module

public import Silmaril.Semantics.Naming.Defs
import Silmaril.Proofs.Semantics.Naming.Basic

public section

namespace Silmaril.Semantics.Naming

variable {Name Payload Wire : Type} {rel other : Relation Name Payload}

theorem fillMissing_binding (base : Binding rel) (defaults : Binding other) :
    Binding (fillMissing rel other) := Proofs.Semantics.Naming.fillMissing_binding base defaults

theorem subset_fillMissing : Subset rel (fillMissing rel other) := fun _ _ hit => .inl hit

theorem Binding.subset (bound : Binding rel) (incl : Subset other rel) : Binding other := by
  intro name left right first second
  exact bound (incl first) (incl second)

theorem Binding.inter (bound : Binding rel) : Binding (inter rel other) :=
  bound.subset (by intro name payload member; exact member.1)

theorem binding_iff_no_collisions : Binding rel ↔ collisions rel = ∅ :=
  Proofs.Semantics.Naming.binding_iff_no_collisions

theorem graph_binding (read : Name → Option Payload) : Binding (graph read) := by
  intro name left right first second
  exact Option.some.inj (first.symm.trans second)

@[simp] theorem mem_names {name : Name} {payload : Payload} :
    name ∈ names rel payload ↔ rel name payload := Iff.rfl

theorem names_eq_singleton_iff {root : Name} {payload : Payload} :
    names rel payload = {root} ↔ rel root payload ∧ ∀ name, rel name payload → name = root := by
  constructor
  · intro eq; change root ∈ names rel payload ∧ ∀ name, name ∈ names rel payload → name = root; rw [eq]; exact ⟨rfl, fun _ hit => hit⟩
  · rintro ⟨hit, unique⟩; exact Set.ext fun _ => ⟨fun named => unique _ named, fun eq => (show _ = root from eq).symm ▸ hit⟩

@[simp] theorem Binding.lookup_eq_some (bound : Binding rel) {name payload} :
    bound.lookup name = some payload ↔ rel name payload :=
  Proofs.Semantics.Naming.lookup_eq_some bound

@[simp] theorem UniqueNames.lookup_eq_some (unique : UniqueNames rel) {name payload} :
    unique.lookup payload = some name ↔ rel name payload := Binding.lookup_eq_some unique

theorem Binding.push (bound : Binding rel) {serializes : Payload → Wire → Prop}
    (deterministic : Binding serializes) : Binding (push rel serializes) :=
  Proofs.Semantics.Naming.push_binding bound deterministic

theorem Binding.project (bound : Binding rel) (decode : Payload → Option Wire) :
    Binding (project rel decode) := bound.push (graph_binding decode)

theorem Binding.lookup_project (bound : Binding rel) (decode : Payload → Option Wire)
    (name : Name) : (bound.project decode).lookup name = (bound.lookup name).bind decode :=
  Proofs.Semantics.Naming.lookup_project bound decode name (bound.project decode)

theorem Binding.quotient (bound : Binding rel) (equiv : Setoid Payload) :
    Binding (quotient rel equiv) := bound.project (fun repr => some (Quotient.mk equiv repr))

theorem mem_names_project {decode : Payload → Option Wire} {name : Name} {value : Wire} :
    name ∈ names (project rel decode) value ↔
      ∃ repr, name ∈ names rel repr ∧ decode repr = some value := Iff.rfl

theorem mem_names_quotient {equiv : Setoid Payload} {name : Name} {repr : Payload} :
    name ∈ names (quotient rel equiv) (Quotient.mk equiv repr) ↔
      ∃ otherRepr, name ∈ names rel otherRepr ∧ equiv.r otherRepr repr :=
  Proofs.Semantics.Naming.mem_names_quotient

theorem names_quotient_congr {equiv : Setoid Payload} {left right : Payload}
    (equivalent : equiv.r left right) :
    names (quotient rel equiv) (Quotient.mk equiv left) =
      names (quotient rel equiv) (Quotient.mk equiv right) :=
  congrArg (names (quotient rel equiv)) (Quotient.sound equivalent)

/-- Canonicality among named representations is sufficient to transfer unique
naming to semantic values. It is not needed for binding or lookup. -/
theorem UniqueNames.project (unique : UniqueNames rel) {decode : Payload → Option Wire}
    (canonical : ∀ ⦃firstName secondName left right value⦄,
      rel firstName left → rel secondName right →
      decode left = some value → decode right = some value → left = right) :
    UniqueNames (project rel decode) :=
  Proofs.Semantics.Naming.project_uniqueNames unique canonical

/-- Use uniqueness on the semantic relation, not on its raw representation store. -/
theorem UniqueNames.payload_ne_of_name_ne (unique : UniqueNames rel)
    {firstName secondName : Name} {left right : Payload}
    (first : firstName ∈ names rel left) (second : secondName ∈ names rel right)
    (different : firstName ≠ secondName) : left ≠ right := by
  rintro rfl
  exact different (unique first second)

/-- A functional parser recovers the particular source of a serialized byte string. -/
theorem push_parse_iff {serializes : Payload → Wire → Prop} {parse : Wire → Option Payload}
    (recovers : ∀ ⦃payload wire⦄, serializes payload wire → parse wire = some payload)
    {name wire payload} (parsed : parse wire = some payload) :
    push rel serializes name wire ↔ rel name payload ∧ serializes payload wire :=
  Proofs.Semantics.Naming.push_parse_iff recovers parsed

theorem hashCompatible_iff_partial {hash : Wire → Name} {bytes : Relation Name Wire} :
    HashCompatible hash bytes ↔ PartialHashCompatible (some ∘ hash) bytes :=
  ⟨fun ok _ _ hit => congrArg some (ok hit), fun ok _ _ hit => Option.some.inj (ok hit)⟩

theorem PartialHashCompatible.not_named_of_none {hash? : Wire → Option Name} {bytes : Relation Name Wire}
    (integrity : PartialHashCompatible hash? bytes) {name : Name} {wire : Wire} (unavailable : hash? wire = none) :
    ¬ bytes name wire := fun hit => Option.some_ne_none name ((integrity hit).symm.trans unavailable)

/-- A fixed deterministic algorithm gives at most one name per byte string.
This is the converse direction to `Binding` and does not rule out collisions. -/
theorem PartialHashCompatible.uniqueNames {hash? : Wire → Option Name} {bytes : Relation Name Wire}
    (integrity : PartialHashCompatible hash? bytes) : UniqueNames bytes := by
  intro wire left right first second
  exact Option.some.inj ((integrity first).symm.trans (integrity second))

theorem HashCompatible.uniqueNames {hash : Wire → Name} {bytes : Relation Name Wire}
    (integrity : HashCompatible hash bytes) : UniqueNames bytes :=
  (hashCompatible_iff_partial.mp integrity).uniqueNames

theorem UniqueNames.of_push {serializes : Payload → Wire → Prop}
    (unique : UniqueNames (push rel serializes)) (total : ∀ payload, ∃ wire, serializes payload wire) :
    UniqueNames rel := by
  intro payload left right first second
  obtain ⟨wire, encoded⟩ := total payload
  exact unique ⟨payload, first, encoded⟩ ⟨payload, second, encoded⟩

theorem Stores.Binding.subset {Obj Blob : Type} {left right : Stores Name Obj Blob}
    (bound : right.Binding) (incl : left.Subset right) : left.Binding :=
  ⟨bound.1.subset incl.1, bound.2.subset incl.2⟩

theorem Stores.Binding.flatten {Obj : Type} {store : Stores Name Obj Wire} (bound : store.Binding)
    (disjoint : store.DisjointDomains) {serializes : Obj → Wire → Prop}
    (deterministic : Naming.Binding serializes) : Naming.Binding (store.flatten serializes) :=
  Proofs.Semantics.Naming.flatten_binding bound disjoint deterministic

theorem Checked.classify_merge (left right : Relation Name Payload) :
    (classify left).merge (classify right) = classify (union left right) :=
  Proofs.Semantics.Naming.classify_merge left right

theorem Checked.merge_assoc (left mid right : Checked Name Payload) :
    (left.merge mid).merge right = left.merge (mid.merge right) :=
  Proofs.Semantics.Naming.merge_assoc left mid right

theorem Checked.merge_comm (left right : Checked Name Payload) : left.merge right = right.merge left :=
  Proofs.Semantics.Naming.merge_comm left right

@[simp] theorem Checked.merge_idem (snapshot : Checked Name Payload) : snapshot.merge snapshot = snapshot :=
  Proofs.Semantics.Naming.merge_idem snapshot

end Silmaril.Semantics.Naming
