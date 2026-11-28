module

public import Silmaril.Logic.Operational.SOS.Thms
public import Silmaril.Wasm.Execution.Memory
public import Silmaril.Wasm.Execution.Runtime

/-! # Isolated Memory32 growth

For an allocated memory, a valid request can append zero-filled pages and
return the previous page count. Failure is always permitted and returns the
all-ones sentinel without changing memory. The Core boundary uses the spec
growth policy and page-aligned legacy buffers.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryGrow

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Execution
open Execution.Runtime (MemInst)

inductive State where
  | request (delta : BitVec 32)
  | grown (bytes : ByteArray)
  | failed

/-- Assumptions needed to read the legacy memory limits and buffer in Core. -/
structure Admitted (m : MemInst) : Prop where
  aligned : m.data.size % Memory.pageSize = 0
  maxFits : ∀ max, m.max = some max → max < 2 ^ 64

/-- Alignment and page limits required for the native success rule. Resource
failure is permitted even when these conditions hold. -/
def SizeAllows (m : MemInst) (delta : Nat) : Prop :=
  m.data.size % Memory.pageSize = 0 ∧ Memory.size m.data + delta ≤ Memory.maxPages ∧
    (m.max.isNone ∨ Memory.size m.data + delta ≤ m.max.getD 0)

inductive Outcome (m : MemInst) : State → State → Prop where
  | grow (delta : BitVec 32) (bytes : ByteArray)
      (sized : Memory.grow? m.data m.max delta.toNat = some bytes) :
      Outcome m (.request delta) (.grown bytes)
  | fail (delta : BitVec 32) : Outcome m (.request delta) .failed

abbrev Judgment := State × State
def shape : SOS.Shape.{0} := ⟨⟨State, Unit⟩, Judgment, fun (a, _, b) => (a, b)⟩
def presentation (m : MemInst) : SOS.Presentation :=
  ⟨shape, {r | r.premises = [] ∧ Outcome m r.conclusion.1 r.conclusion.2}⟩

abbrev Edge (m : MemInst) (a b : State) := (presentation m).Derives (a, b)
abbrev Runs (m : MemInst) := Relation.ReflTransGen (Edge m)

end Silmaril.Wasm.Institution.Operational.MemoryGrow
