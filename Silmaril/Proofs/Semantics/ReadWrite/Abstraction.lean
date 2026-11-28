module

public import Silmaril.Semantics.ReadWrite.Abstraction.Defs
public import Silmaril.Semantics.ReadWrite.Thms

public section
namespace Silmaril.Proofs.Semantics.ReadWrite.Abstraction

open Silmaril.Semantics.ReadWrite

universe u v
variable {Address : Type u} {Value : Type v}

theorem eraseValues_reads (trace : Trace Address Value) :
    trace.eraseValues.reads = trace.reads.map Prod.fst := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
    cases event <;>
      simp_all [Trace.eraseValues, AddressTrace.reads, Trace.reads, Event.eraseValue]

theorem eraseValues_writes (trace : Trace Address Value) :
    trace.eraseValues.writes = trace.writes.map Prod.fst := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
    cases event <;>
      simp_all [Trace.eraseValues, AddressTrace.writes, Trace.writes, Event.eraseValue]

theorem accessSets_eraseValues (trace : Trace Address Value) :
    trace.eraseValues.accessSets = trace.accessSets := by
  apply AccessSets.ext <;> apply Set.ext <;> intro address
  · change address ∈ trace.eraseValues.reads ↔ trace.Reads address
    rw [eraseValues_reads, List.mem_map]
    exact ⟨fun ⟨⟨_, value⟩, mem, eq⟩ => ⟨value, eq ▸ mem⟩,
      fun ⟨value, mem⟩ => ⟨(address, value), mem, rfl⟩⟩
  · change address ∈ trace.eraseValues.writes ↔ trace.Defs address
    rw [eraseValues_writes, List.mem_map]
    exact ⟨fun ⟨⟨_, value⟩, mem, eq⟩ => ⟨value, eq ▸ mem⟩,
      fun ⟨value, mem⟩ => ⟨(address, value), mem, rfl⟩⟩

theorem accessSets_append (first last : AddressTrace Address) :
    (first ++ last).accessSets = first.accessSets * last.accessSets := by
  apply AccessSets.ext <;> apply Set.ext <;> intro address
  · change address ∈ (first ++ last).reads ↔ address ∈ first.reads ∨ address ∈ last.reads
    simp [AddressTrace.reads, List.filterMap_append]
  · change address ∈ (first ++ last).writes ↔ address ∈ first.writes ∨ address ∈ last.writes
    simp [AddressTrace.writes, List.filterMap_append]

theorem trace_useDef_append (first last : Trace Address Value) :
    Trace.useDef (first ++ last) = first.useDef * last.useDef := by
  apply UseDef.ext <;> apply Set.ext <;> intro address
  · exact Trace.uses_append.trans (or_congr Iff.rfl and_comm)
  · exact Trace.defs_append

theorem useDef_eraseValues (trace : Trace Address Value) :
    trace.eraseValues.useDef = trace.useDef := by
  induction trace with
  | nil =>
    change (1 : UseDef Address) = Trace.useDef ([] : Trace Address Value)
    exact UseDef.ext rfl (Set.ext fun _ => ⟨False.elim, fun ⟨_, mem⟩ => List.not_mem_nil mem⟩)
  | cons event rest ih =>
    change FreeMonoid.lift AddressEvent.useDef
      (FreeMonoid.ofList (event.eraseValue :: Trace.eraseValues rest)) = Trace.useDef ([event] ++ rest)
    rw [FreeMonoid.ofList_cons, map_mul, FreeMonoid.lift_eval_of, trace_useDef_append]
    change event.eraseValue.useDef * (Trace.eraseValues rest).useDef =
      Trace.useDef [event] * Trace.useDef rest
    rw [ih]
    congr 1
    cases event <;> apply UseDef.ext <;> apply Set.ext <;> intro address <;>
      simp [Event.eraseValue, AddressEvent.useDef, Trace.useDef, Trace.Uses, Trace.Defs, Trace.writes]

theorem useDef_footprint_mul (first last : UseDef Address) :
    (first * last).footprint = first.footprint ∪ last.footprint := by
  apply Set.ext
  intro address
  change address ∈ (first.uses ∪ (last.uses \ first.defs)) ∪ (first.defs ∪ last.defs) ↔
    address ∈ (first.uses ∪ first.defs) ∪ (last.uses ∪ last.defs)
  simp only [Set.mem_union, Set.mem_sdiff]
  grind

theorem uses_not_factor_through_accessSets (address : Address) (value : Value) :
    ¬ ∃ f : AccessSets Address → Set Address,
      ∀ trace : Trace Address Value, f trace.accessSets = trace.useDef.uses := by
  rintro ⟨f, factor⟩
  let readFirst : Trace Address Value := [.read address value, .write address value]
  let writeFirst : Trace Address Value := [.write address value, .read address value]
  have same : readFirst.accessSets = writeFirst.accessSets := rfl
  have equalUses : readFirst.useDef.uses = writeFirst.useDef.uses :=
    (factor readFirst).symm.trans ((congrArg f same).trans (factor writeFirst))
  have used : address ∈ readFirst.useDef.uses := Or.inl rfl
  rw [equalUses] at used
  exact used.1 rfl

theorem reads_not_factor_through_useDef (address : Address) (value : Value) :
    ¬ ∃ f : UseDef Address → Set Address,
      ∀ trace : Trace Address Value, f trace.useDef = trace.accessSets.reads := by
  rintro ⟨f, factor⟩
  let writeOnly : Trace Address Value := [.write address value]
  let writeRead : Trace Address Value := [.write address value, .read address value]
  have same : writeOnly.useDef = writeRead.useDef := by
    refine UseDef.ext (Set.ext fun other => ?_) rfl
    change (other ≠ address ∧ False) ↔ other ≠ address ∧ (other = address ∨ False)
    simp
  have read : address ∈ writeRead.accessSets.reads := ⟨value, List.mem_cons_self⟩
  rw [← factor writeRead, ← same, factor writeOnly] at read
  exact read.elim fun _ mem => List.not_mem_nil mem

end Silmaril.Proofs.Semantics.ReadWrite.Abstraction
