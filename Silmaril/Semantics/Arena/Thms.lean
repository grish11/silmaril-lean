module

public import Mathlib.Logic.Equiv.Defs
public import Silmaril.Semantics.Arena.Defs
public import Silmaril.Semantics.Naming.Thms
import Silmaril.Proofs.Semantics.Arena.Basic
import Silmaril.Proofs.Semantics.Arena.Packed

public section

namespace Silmaril.Semantics.Arena

variable {Key Name Payload : Type} {limit : Nat}

namespace State

theorem step_spec [DecidableEq Key] {arena target : State Key Name Payload} {key : Key} {edit : Edit Name Payload} :
    arena.step key edit = .ok target ↔
      edit.apply (arena key) = .ok (target key) ∧ ∀ query, key ≠ query → target query = arena query :=
  Proofs.Semantics.Arena.step_spec

theorem step_error_iff [DecidableEq Key] (arena : State Key Name Payload) (key : Key) (edit : Edit Name Payload)
    (fault : Fault) : arena.step key edit = .error fault ↔ edit.apply (arena key) = .error fault := by
  cases applied : edit.apply (arena key) <;> simp [step, Except.map, applied]

theorem write_read [DecidableEq Key] {arena target : State Key Name Payload} {key : Key}
    {assign : Payload → Option Name} {payload : Payload} (stepped : arena.step key (.write assign payload) = .ok target) :
    target key = some ⟨assign payload, some payload⟩ :=
  Proofs.Semantics.Arena.write_read stepped

/-- From an admitted state, the only possible new witness is at the changed
key. Releases do not remove anything from the reference CAS. -/
theorem admitted_step_iff [DecidableEq Key] {arena target : State Key Name Payload} {key : Key} {edit : Edit Name Payload}
    {reference : Naming.Relation Name Payload} (original : arena.AdmittedBy reference)
    (stepped : arena.step key edit = .ok target) :
    target.AdmittedBy reference ↔ ∀ name payload, target key = some ⟨some name, some payload⟩ → reference name payload :=
  Proofs.Semantics.Arena.admitted_step_iff original stepped

theorem admitted_write_iff [DecidableEq Key] {arena target : State Key Name Payload} {key : Key}
    {assign : Payload → Option Name} {payload : Payload} {reference : Naming.Relation Name Payload}
    (original : arena.AdmittedBy reference) (stepped : arena.step key (.write assign payload) = .ok target) :
    target.AdmittedBy reference ↔ ∀ name, assign payload = some name → reference name payload :=
  Proofs.Semantics.Arena.admitted_write_iff original stepped

theorem observations_binding {arena : State Key Name Payload} {reference : Naming.Relation Name Payload}
    (admitted : arena.AdmittedBy reference) (bound : Naming.Binding reference) : Naming.Binding arena.observations :=
  bound.subset admitted

end State

namespace Bounded

@[simp] theorem read_toDense (arena : Bounded limit Name Payload) (index : Nat) : arena.toDense.read index = arena.val index :=
  Proofs.Semantics.Arena.read_toDense arena index

/-- Within the bound, the restricted transition is the raw key transition. -/
theorem step_abstract (arena : Bounded limit Name Payload) {index : Nat} (inside : index < limit)
    (edit : Edit Name Payload) : (arena.step index edit).map Subtype.val = arena.val.step index edit :=
  Proofs.Semantics.Arena.bounded_step_abstract arena inside edit

theorem append_fresh (arena : Bounded limit Name Payload) (next : Slot Name Payload) :
    arena.val limit = none ∧ (arena.append next).val limit = some next :=
  ⟨arena.property limit (Nat.le_refl limit), by simp [append, State.replaceAt]⟩

theorem append_read_old (arena : Bounded limit Name Payload) (next : Slot Name Payload) {index : Nat}
    (inside : index < limit) : (arena.append next).val index = arena.val index := by
  simp [append, State.replaceAt, (Nat.ne_of_lt inside).symm]

end Bounded

namespace Dense

/-- Exact equivalence at fixed capacity. The array length also records any
trailing holes; it is not recovered by counting occupied slots. -/
def equivBounded : Dense limit Name Payload ≃ Bounded limit Name Payload where
  toFun := toBounded
  invFun := Bounded.toDense
  left_inv := Proofs.Semantics.Arena.dense_roundtrip
  right_inv arena := Subtype.ext (funext arena.read_toDense)

/-- The same success, vacancy/occupancy fault, or bounds fault is observed
by both representations. -/
theorem step_commutes (arena : Dense limit Name Payload) (index : Nat) (edit : Edit Name Payload) :
    (arena.step index edit).map Dense.toBounded = arena.toBounded.step index edit :=
  Proofs.Semantics.Arena.step_commutes arena index edit

theorem append_commutes (arena : Dense limit Name Payload) (next : Slot Name Payload) :
    (arena.append next).toBounded = arena.toBounded.append next :=
  Proofs.Semantics.Arena.append_commutes arena next

@[simp] theorem packed_read (slots : Array (Slot Name Payload)) (index : Nat) : (packed slots).read index = slots[index]? :=
  Proofs.Semantics.Arena.packed_read slots index

theorem ext_read {left right : Dense limit Name Payload} (same : ∀ index, left.read index = right.read index) :
    left = right := equivBounded.injective (Subtype.ext (funext same))

@[simp] theorem read_ofFn (cells : Fin limit → Option (Slot Name Payload)) (index : Fin limit) :
    Dense.read ⟨Array.ofFn cells, Array.size_ofFn⟩ index = cells index :=
  Proofs.Semantics.Arena.read_ofFn cells index

@[simp] theorem packExact_read (slots : { slots : Array (Slot Name Payload) // slots.size = limit }) (index : Nat) :
    (packExact slots).read index = slots.val[index]? := Proofs.Semantics.Arena.packExact_read slots index

theorem packExact_noHoles (slots : { slots : Array (Slot Name Payload) // slots.size = limit }) :
    (packExact slots).NoHoles := Proofs.Semantics.Arena.packExact_noHoles slots

/-- The plain array alternative has precisely the no-hole domain, at the same capacity. -/
def equivPacked : { arena : Dense limit Name Payload // arena.NoHoles } ≃
    { slots : Array (Slot Name Payload) // slots.size = limit } where
  toFun arena := arena.val.unpack arena.property
  invFun slots := ⟨packExact slots, packExact_noHoles slots⟩
  left_inv arena := Subtype.ext (ext_read (Proofs.Semantics.Arena.read_packExact_unpack arena.val arena.property))
  right_inv := Proofs.Semantics.Arena.unpack_packExact

end Dense
end Silmaril.Semantics.Arena
