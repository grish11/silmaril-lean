module

public import Silmaril.Process.Memory.Trace.Defs

/-! Separate read-only and write-only byte traces for process memory. -/

@[expose] public section
namespace Silmaril.Process.Memory

open Silmaril.Semantics.ReadWrite

/-- An ordered list of observed byte values. Replay validates them without
changing the memory. -/
structure ByteReadTrace where
  observations : ReadTrace Nat Byte

/-- An ordered list of byte assignments. Replay checks write permissions and
applies the assignments in order. -/
structure ByteWriteTrace where
  assignments : WriteTrace Nat Byte

def readProjection (trace : Trace Nat Byte) : ByteReadTrace := ⟨trace.reads⟩
def writeProjection (trace : Trace Nat Byte) : ByteWriteTrace := ⟨trace.writes⟩

namespace ByteReadTrace

def toTrace (reads : ByteReadTrace) : Trace Nat Byte := reads.observations.toTrace

def Replays (reads : ByteReadTrace) (before after : Memory) : Prop :=
  reads.toTrace.Replays byteAccess before after

def run (reads : ByteReadTrace) (before : Memory) : Option Memory :=
  reads.toTrace.run byteAccess before

end ByteReadTrace

namespace ByteWriteTrace

def toTrace (writes : ByteWriteTrace) : Trace Nat Byte := writes.assignments.toTrace

def Replays (writes : ByteWriteTrace) (before after : Memory) : Prop :=
  writes.toTrace.Replays byteAccess before after

def run (writes : ByteWriteTrace) (before : Memory) : Option Memory :=
  writes.toTrace.run byteAccess before

end ByteWriteTrace

end Silmaril.Process.Memory
