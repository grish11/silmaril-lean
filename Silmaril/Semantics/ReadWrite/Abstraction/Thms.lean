module

public import Silmaril.Semantics.ReadWrite.Abstraction.Defs
public import Silmaril.Semantics.ReadWrite.Thms
import Silmaril.Proofs.Semantics.ReadWrite.Abstraction

public section
namespace Silmaril.Semantics.ReadWrite

universe u v
variable {Address : Type u} {Value : Type v}

@[simp] theorem Trace.eraseValues_append (first last : Trace Address Value) :
    Trace.eraseValues (first ++ last) = first.eraseValues ++ last.eraseValues :=
  List.map_append

@[simp] theorem Trace.eraseValues_reads (trace : Trace Address Value) :
    trace.eraseValues.reads = trace.reads.map Prod.fst :=
  Proofs.Semantics.ReadWrite.Abstraction.eraseValues_reads trace

@[simp] theorem Trace.eraseValues_writes (trace : Trace Address Value) :
    trace.eraseValues.writes = trace.writes.map Prod.fst :=
  Proofs.Semantics.ReadWrite.Abstraction.eraseValues_writes trace

@[simp] theorem Trace.accessSets_eraseValues (trace : Trace Address Value) :
    trace.eraseValues.accessSets = trace.accessSets :=
  Proofs.Semantics.ReadWrite.Abstraction.accessSets_eraseValues trace

theorem AddressTrace.accessSets_append (first last : AddressTrace Address) :
    (first ++ last).accessSets = first.accessSets * last.accessSets :=
  Proofs.Semantics.ReadWrite.Abstraction.accessSets_append first last

theorem Trace.accessSets_append (first last : Trace Address Value) :
    Trace.accessSets (first ++ last) = first.accessSets * last.accessSets := by
  rw [← Trace.accessSets_eraseValues (first ++ last), Trace.eraseValues_append,
    AddressTrace.accessSets_append, Trace.accessSets_eraseValues, Trace.accessSets_eraseValues]

theorem AddressTrace.useDef_append (first last : AddressTrace Address) :
    (first ++ last).useDef = first.useDef * last.useDef := by
  unfold AddressTrace.useDef
  rw [FreeMonoid.ofList_append, map_mul]

@[simp] theorem Trace.useDef_eraseValues (trace : Trace Address Value) :
    trace.eraseValues.useDef = trace.useDef :=
  Proofs.Semantics.ReadWrite.Abstraction.useDef_eraseValues trace

theorem Trace.useDef_append (first last : Trace Address Value) :
    Trace.useDef (first ++ last) = first.useDef * last.useDef :=
  Proofs.Semantics.ReadWrite.Abstraction.trace_useDef_append first last

@[simp] theorem Trace.mem_accessSets_reads (trace : Trace Address Value) (address : Address) :
    address ∈ trace.accessSets.reads ↔ trace.Reads address := Iff.rfl

@[simp] theorem Trace.mem_accessSets_defs (trace : Trace Address Value) (address : Address) :
    address ∈ trace.accessSets.defs ↔ trace.Defs address := Iff.rfl

@[simp] theorem Trace.mem_useDef_uses (trace : Trace Address Value) (address : Address) :
    address ∈ trace.useDef.uses ↔ trace.Uses address := Iff.rfl

@[simp] theorem Trace.mem_useDef_defs (trace : Trace Address Value) (address : Address) :
    address ∈ trace.useDef.defs ↔ trace.Defs address := Iff.rfl

@[simp] theorem Trace.accessSets_footprint (trace : Trace Address Value) :
    trace.accessSets.footprint = {address | trace.Footprint address} := rfl

@[simp] theorem Trace.useDef_footprint (trace : Trace Address Value) :
    trace.useDef.footprint = {address | trace.Footprint address} :=
  Set.ext fun _ => Trace.uses_or_defs

theorem UseDef.footprint_mul (first last : UseDef Address) :
    (first * last).footprint = first.footprint ∪ last.footprint :=
  Proofs.Semantics.ReadWrite.Abstraction.useDef_footprint_mul first last

/-- Reversing a read and a write at the same address can change its initial uses. -/
theorem Trace.uses_not_factor_through_accessSets (address : Address) (value : Value) :
    ¬ ∃ f : AccessSets Address → Set Address,
      ∀ trace : Trace Address Value, f trace.accessSets = trace.useDef.uses :=
  Proofs.Semantics.ReadWrite.Abstraction.uses_not_factor_through_accessSets address value

/-- Appending a read of a value already written can change the set of all reads
while leaving the use/def summary the same. -/
theorem Trace.reads_not_factor_through_useDef (address : Address) (value : Value) :
    ¬ ∃ f : UseDef Address → Set Address,
      ∀ trace : Trace Address Value, f trace.useDef = trace.accessSets.reads :=
  Proofs.Semantics.ReadWrite.Abstraction.reads_not_factor_through_useDef address value

end Silmaril.Semantics.ReadWrite
