module

public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryGrow

open Silmaril.Semantics.SOS
open Execution
open Execution.Runtime (MemInst)

theorem fact {m : MemInst} {a b : State} (h : Outcome m a b) : Edge m a b :=
  Derives.apply (R := (presentation m).rules) (r := ⟨[], (a, b)⟩) ⟨rfl, h⟩ (fun _ h => nomatch h)

theorem invert {m : MemInst} {a b : State} (e : Edge m a b) : Outcome m a b :=
  Derives.least (M := fun j => Outcome m j.1 j.2) e (fun _ hr _ => hr.2)

/-- The pure growth candidate exists exactly on an aligned, in-limit request. -/
theorem grow_eq_some_iff {m : MemInst} {delta : Nat} {bytes : ByteArray} :
    Memory.grow? m.data m.max delta = some bytes ↔
      SizeAllows m delta ∧ bytes = m.data ++ ⟨Array.replicate (delta * Memory.pageSize) 0⟩ := by
  unfold Memory.grow? SizeAllows
  split
  · rename_i yes
    simp only [Option.some.injEq, yes, true_and]
    exact eq_comm
  · rename_i no
    constructor
    · intro h
      cases h
    · intro h
      exact (no h.1).elim

/-- A successful growth appends exactly `delta` zero-filled pages. -/
theorem grown_bytes {m : MemInst} {delta : BitVec 32} {bytes : ByteArray}
    (edge : Edge m (.request delta) (.grown bytes)) :
    bytes = m.data ++ ⟨Array.replicate (delta.toNat * Memory.pageSize) 0⟩ := by
  cases invert edge with
  | grow _ _ h => exact (grow_eq_some_iff.mp h).2

theorem grown_pages {m : MemInst} {delta : BitVec 32} {bytes : ByteArray}
    (edge : Edge m (.request delta) (.grown bytes)) :
    Memory.size bytes = Memory.size m.data + delta.toNat := by
  cases invert edge with
  | grow delta bytes h =>
    simp only [Memory.size, Memory.grow_size _ _ _ _ h]
    rw [Nat.add_mul_div_right _ _ (by decide : 0 < Memory.pageSize)]

end Silmaril.Wasm.Institution.Operational.MemoryGrow
