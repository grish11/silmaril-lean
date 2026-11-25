module

public import Silmaril.Logic.Operational.SOS.Thms
public import Silmaril.Wasm.Execution.Memory

/-!
# Queries of one memory32 instance

The isolated queries are `memory.size` and full-width `i32.load` at zero
static offset. The memory is supplied as bytes. An out-of-bounds load yields
the administrative trap; a missing memory is outside the native image.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryQuery

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution

inductive State where
  | size
  | load (address : BitVec 32)
  | value (bits : BitVec 32)
  | trap

abbrev Judgment := State × State

inductive RuleInstance (bytes : ByteArray) : Rule Judgment → Prop where
  | size : RuleInstance bytes ⟨[], (.size, .value (BitVec.ofNat 32 (Memory.size bytes)))⟩
  | load (address bits : BitVec 32) (read : Memory.load bytes address.toNat 4 = some bits) :
      RuleInstance bytes ⟨[], (.load address, .value bits)⟩
  | loadTrap (address : BitVec 32) (bound : bytes.size < address.toNat + 4) :
      RuleInstance bytes ⟨[], (.load address, .trap)⟩

def shape : SOS.Shape.{0} := ⟨⟨State, Unit⟩, Judgment, fun (a, _, b) => (a, b)⟩
def presentation (bytes : ByteArray) : SOS.Presentation := ⟨shape, {r | RuleInstance bytes r}⟩

abbrev Edge (bytes : ByteArray) (a b : State) := (presentation bytes).Derives (a, b)

end Silmaril.Wasm.Institution.Operational.MemoryQuery
