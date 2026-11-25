module

public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryQuery.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryQuery

open Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution

theorem fact {bytes : ByteArray} {a b : State} (h : RuleInstance bytes ⟨[], (a, b)⟩) :
    Edge bytes a b :=
  Derives.apply (R := (presentation bytes).rules) (r := ⟨[], (a, b)⟩) h (fun _ h => nomatch h)

theorem invert {bytes : ByteArray} {a b : State} (edge : Edge bytes a b) :
    RuleInstance bytes ⟨[], (a, b)⟩ := Proofs.invert edge

theorem load_none_iff {bytes : ByteArray} {address : BitVec 32} :
    Memory.load bytes address.toNat 4 = none ↔ bytes.size < address.toNat + 4 :=
  Proofs.load_none_iff

end Silmaril.Wasm.Institution.Operational.MemoryQuery
