module

public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryQuery.Proofs

open Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution

theorem invert {bytes : ByteArray} {a b : State} (edge : Edge bytes a b) :
    RuleInstance bytes ⟨[], (a, b)⟩ := by
  refine Derives.least (M := fun j => RuleInstance bytes ⟨[], j⟩) edge ?_
  intro r member _
  change RuleInstance bytes r at member
  cases member with
  | size => exact .size
  | load a v h => exact .load a v h
  | loadTrap a h => exact .loadTrap a h

theorem load_none_iff {bytes : ByteArray} {address : BitVec 32} :
    Memory.load bytes address.toNat 4 = none ↔ bytes.size < address.toNat + 4 := by
  by_cases bound : address.toNat + 4 ≤ bytes.size <;>
    simp [Memory.load, Memory.readBytes, bound, Nat.not_lt.mpr, Nat.lt_of_not_ge]

end Silmaril.Wasm.Institution.Operational.MemoryQuery.Proofs
