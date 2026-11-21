module

public import Silmaril.Semantics.Arena.Defs

public section

namespace Silmaril.Proofs.Semantics.Arena

open Silmaril.Semantics.Arena

variable {Key Name Payload : Type} {limit : Nat}

theorem step_spec [DecidableEq Key] {arena target : State Key Name Payload} {key : Key} {edit : Edit Name Payload} :
    arena.step key edit = .ok target ↔
      edit.apply (arena key) = .ok (target key) ∧ ∀ query, key ≠ query → target query = arena query := by
  constructor
  · intro stepped
    cases applied : edit.apply (arena key) with
    | error fault => simp [State.step, applied, Except.map] at stepped
    | ok next =>
      have same : arena.replaceAt key next = target := by simpa [State.step, applied, Except.map] using stepped
      subst target
      exact ⟨by simp [State.replaceAt], fun query different => by simp [State.replaceAt, different]⟩
  · rintro ⟨applied, frame⟩
    rw [State.step, applied, Except.map]
    congr 1
    funext query
    by_cases same : key = query
    · subst query
      simp [State.replaceAt]
    · simp [State.replaceAt, same, frame query same]

theorem write_read [DecidableEq Key] {arena target : State Key Name Payload} {key : Key}
    {assign : Payload → Option Name} {payload : Payload} (stepped : arena.step key (.write assign payload) = .ok target) :
    target key = some ⟨assign payload, some payload⟩ := by
  have applied := (step_spec.mp stepped).1
  cases old : arena key <;> simp [old, Edit.write, Edit.apply] at applied
  exact applied.symm

theorem admitted_step_iff [DecidableEq Key] {arena target : State Key Name Payload} {key : Key} {edit : Edit Name Payload}
    {reference : Silmaril.Semantics.Naming.Relation Name Payload}
    (original : arena.AdmittedBy reference) (stepped : arena.step key edit = .ok target) :
    target.AdmittedBy reference ↔ ∀ name payload, target key = some ⟨some name, some payload⟩ → reference name payload := by
  refine ⟨fun admitted _ _ hit => admitted ⟨key, hit⟩, ?_⟩
  intro localSound name payload witness
  obtain ⟨query, present⟩ := witness
  by_cases same : key = query
  · exact localSound name payload (same ▸ present)
  · exact original ⟨query, ((step_spec.mp stepped).2 query same).symm ▸ present⟩

theorem admitted_write_iff [DecidableEq Key] {arena target : State Key Name Payload} {key : Key}
    {assign : Payload → Option Name} {payload : Payload} {reference : Silmaril.Semantics.Naming.Relation Name Payload}
    (original : arena.AdmittedBy reference) (stepped : arena.step key (.write assign payload) = .ok target) :
    target.AdmittedBy reference ↔ ∀ name, assign payload = some name → reference name payload := by
  rw [admitted_step_iff original stepped, write_read stepped]
  constructor
  · intro admitted name named
    exact admitted name payload (by rw [named])
  · intro allowed name value equal
    have cell := Option.some.inj equal
    have same := Option.some.inj (congrArg Slot.payload cell)
    exact same ▸ allowed name (congrArg Slot.name cell)

theorem read_toDense (arena : Bounded limit Name Payload) (index : Nat) :
    arena.toDense.read index = arena.val index := by
  by_cases inside : index < limit
  · have inArray : index < arena.toDense.val.size := arena.toDense.property.symm ▸ inside
    rw [Dense.read, Array.getElem?_eq_getElem inArray]
    simp [Bounded.toDense]
  · have outside := Nat.le_of_not_gt inside
    rw [Dense.read, Array.getElem?_eq_none (arena.toDense.property.symm ▸ outside)]
    exact (arena.property index outside).symm

private theorem cell_eq_some_read (arena : Dense limit Name Payload) {index : Nat} (inside : index < limit) :
    arena.val[index]? = some (arena.read index) := by
  have inArray : index < arena.val.size := arena.property.symm ▸ inside
  simp [Dense.read, Array.getElem?_eq_getElem inArray]

theorem dense_roundtrip (arena : Dense limit Name Payload) : arena.toBounded.toDense = arena := by
  apply Subtype.ext
  apply Array.ext_getElem?
  intro index
  by_cases inside : index < limit
  · rw [cell_eq_some_read arena.toBounded.toDense inside, cell_eq_some_read arena inside, read_toDense]
    rfl
  · have outside := Nat.le_of_not_gt inside
    rw [Array.getElem?_eq_none (arena.toBounded.toDense.property.symm ▸ outside),
      Array.getElem?_eq_none (arena.property.symm ▸ outside)]

private theorem replace_commutes (arena : Dense limit Name Payload) {index : Nat} (inside : index < limit)
    (next : Option (Slot Name Payload)) : (arena.replaceAt index next).toBounded = arena.toBounded.replaceAt index inside next := by
  apply Subtype.ext
  funext query
  have inArray : index < arena.val.size := arena.property.symm ▸ inside
  change (arena.replaceAt index next).read query = State.replaceAt arena.read index next query
  by_cases same : index = query
  · subst query
    simp [Dense.read, Dense.replaceAt, State.replaceAt, inArray]
  · simp [Dense.read, Dense.replaceAt, State.replaceAt, same]

theorem step_commutes (arena : Dense limit Name Payload) (index : Nat) (edit : Edit Name Payload) :
    (arena.step index edit).map Dense.toBounded = arena.toBounded.step index edit := by
  by_cases inside : index < limit
  · simp only [Dense.step, ite_eq_left inside, Bounded.step, dite_eq_left inside]
    change ((edit.apply (arena.read index)).map (arena.replaceAt index)).map Dense.toBounded =
      (edit.apply (arena.read index)).map (arena.toBounded.replaceAt index inside)
    cases edit.apply (arena.read index) with
    | error _ => rfl
    | ok next => exact congrArg Except.ok (replace_commutes arena inside next)
  · simp [Dense.step, Bounded.step, inside, Except.map]

theorem bounded_step_abstract (arena : Bounded limit Name Payload) {index : Nat} (inside : index < limit)
    (edit : Edit Name Payload) : (arena.step index edit).map Subtype.val = arena.val.step index edit := by
  simp only [Bounded.step, dite_eq_left inside, State.step]
  cases edit.apply (arena.val index) <;> rfl

theorem append_commutes (arena : Dense limit Name Payload) (next : Slot Name Payload) :
    (arena.append next).toBounded = arena.toBounded.append next := by
  apply Subtype.ext
  funext query
  change (arena.append next).read query = State.replaceAt arena.read limit (some next) query
  simp only [Dense.read, Dense.append, State.replaceAt, Array.getElem?_push, arena.property]
  by_cases same : query = limit
  · subst query
    simp
  · simp [same, Ne.symm same]

theorem packed_read (slots : Array (Slot Name Payload)) (index : Nat) : (Dense.packed slots).read index = slots[index]? := by
  cases hit : slots[index]? <;> simp [Dense.read, Dense.packed, hit]

end Silmaril.Proofs.Semantics.Arena
