module
public import Silmaril.Elf.Corpus.CjsonInsert.Context.Defs
open Silmaril.Cerberus
open Silmaril.Elf.Corpus.CjsonInsert
namespace CjsonInsertObservationTests
/-- Original caller metadata cannot be hidden by private allocation bookkeeping. -/
theorem caller_metadata_rejected (i : Context.Input) (before after : Mem.Concrete.State)
    (changed : before.allocations.lookup 3 ≠ after.allocations.lookup 3) :
    ¬ Context.callerUpdate i before after := by
  rintro ⟨_, _, _, _, _, allocations, _, _, _⟩
  exact changed (allocations 3 (by omega) (by omega)).1
/-- A change to a byte of the unrelated sixth caller object is rejected. -/
theorem unrelated_byte_rejected (i : Context.Input) (before after expected : Mem.Concrete.State)
    (computed : Context.expectedMemory i before = .ok expected)
    (changed : after.bytes.lookup ((i.base+352 : Nat) : Int) ≠
      expected.bytes.lookup ((i.base+352 : Nat) : Int)) :
    ¬ Context.callerUpdate i before after := by
  rintro ⟨actual, hactual, _, _, _, _, bytes, _, _⟩
  have same : actual = expected := Except.ok.inj (hactual.symm.trans computed)
  subst actual
  exact changed (bytes 352 (by omega)).1
/-- Output remains visible even when fresh helper objects have been cleaned up. -/
theorem stdout_rejected (i : Context.Input) (before after : Mem.Concrete.State)
    (changed : before.stdout ≠ after.stdout) : ¬ Context.callerUpdate i before after := by
  rintro ⟨_, _, _, _, output, _, _, _, _⟩
  exact changed output
end CjsonInsertObservationTests
