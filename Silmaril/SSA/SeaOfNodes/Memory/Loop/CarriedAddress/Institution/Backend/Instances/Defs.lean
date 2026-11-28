module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom.Thms

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend

open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded)
open Silmaril.MLIR.MemRef (Buffer)

/-- The word and heap in the nested RVSDG result tuple. -/
def runtimeResult (cells : Nat) : (Word × Heap cells) ≃ Tuple (WireVal cells) (Threaded wordPorts) where
  toFun result := encodeResult result.1 result.2
  invFun
    | .cons word (.cons heap .nil) => (word, heap)
  left_inv _ := rfl
  right_inv
    | .cons _ (.cons _ .nil) => rfl

/-- The full cell function in the ordered MemRef state. -/
def buffer (cells : Nat) : Heap cells ≃ Buffer cells where
  toFun := Buffer.mk
  invFun := Buffer.cell
  left_inv _ := rfl
  right_inv _ := rfl

/-- Observe the emitted nested RVSDG programs at validated raw entries. -/
noncomputable def rvsdg : Backend where
  Sentence := RuntimeRoom.Sentence
  emit := RuntimeRoom.lowerEquation
  source e := ⟨e.lhs.source, e.rhs.source⟩
  source_emit _ := rfl
  emit_source := by
    rintro _ ⟨⟨lhs, _, rfl⟩, ⟨rhs, _, rfl⟩⟩
    rfl
  Initial := Heap
  Result cells := Tuple (WireVal cells) (Threaded wordPorts)
  initial _ := Equiv.refl _
  result := runtimeResult
  observe e side model heap := RuntimeEntry.observeProgram
    (match side with | .lhs => e.lhs.program | .rhs => e.rhs.program)
    (RuntimeRoom.modelEntry model heap).val
  correct e side model heap value := by
    cases side
    · exact runtimeObserve_eq_some_iff_native e.lhs model heap value.1 value.2
    · exact runtimeObserve_eq_some_iff_native e.rhs model heap value.1 value.2

/-- Observe the emitted ordered MemRef CFGs on their initialized buffers. -/
noncomputable def memref : Backend where
  Sentence := MemRefRoom.Sentence
  emit := MemRefRoom.lowerEquation
  source e := ⟨e.lhs.source, e.rhs.source⟩
  source_emit _ := rfl
  emit_source := by
    rintro _ ⟨⟨lhs, _, rfl⟩, ⟨rhs, _, rfl⟩⟩
    rfl
  Initial := Buffer
  Result cells := Word × Buffer cells
  initial := buffer
  result cells := Equiv.prodCongr (Equiv.refl _) (buffer cells)
  observe e side model initial :=
    match side with
    | .lhs => e.lhs.observe model initial
    | .rhs => e.rhs.observe model initial
  correct e side model heap value := by
    cases side
    · exact MemRefRoom.GeneratedProgram.observe_eq_some_iff_native _ model ⟨heap⟩ (value.1, ⟨value.2⟩)
    · exact MemRefRoom.GeneratedProgram.observe_eq_some_iff_native _ model ⟨heap⟩ (value.1, ⟨value.2⟩)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend
