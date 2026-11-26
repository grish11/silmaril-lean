module

public import Silmaril.Process.Memory
public import Silmaril.Semantics.ReadWrite.Defs

/-! Address-level traces of byte reads and writes on process memory. -/

@[expose] public section
namespace Silmaril.Process.Memory

open Silmaril.Semantics

/-- Check one byte using the process mapping permissions and backing store.
One event touches exactly one address. Writes use the native single-byte update. -/
def byteAccess : ReadWrite.Access Nat Byte Memory where
  read memory address := (memory.readBytes address 1).bind List.head?
  write memory address value := memory.writeBytes address [value]

end Silmaril.Process.Memory
