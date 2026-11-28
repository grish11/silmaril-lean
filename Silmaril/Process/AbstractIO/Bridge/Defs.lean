module

public import Silmaril.Process.AbstractIO.Defs
public import Silmaril.Process.Model.Defs
public import Silmaril.Process.TypedSyscall.Linux.Defs

/-! Partial data maps at the boundary with the ABI-facing process models. -/

@[expose] public section

namespace Silmaril.Process.AbstractIO

/-- Drop the output address of a byte-stream read. For a write, a caller-supplied
copy-in must provide the entire requested buffer. Exit is outside the slice. -/
def ofByteStreamRequest (copyIn : Nat → Nat → Option Bytes) :
    TypedSyscall.Linux.signature.Request → Option Request
  | .read fd _ count => some (.read fd count)
  | .write fd address count => do
    let bytes ← copyIn address count
    if bytes.length = count then some (.write fd bytes) else none
  | .exit _ => none

/-- The ABI-facing byte-stream return value carries the count or errno.
For reads, the bytes must be delivered by a separate copy-out. -/
def byteStreamResult : (req : Request) → Response req → Option Syscall.Result
  | .read .., .ok bytes => some (.ok bytes.length)
  | .read .., .error errno => some (.error errno)
  | .write .., .ok count => some (.ok count)
  | .write .., .error errno => some (.error errno)
  | _, _ => none

/-- Project one non-append regular LPS entry to its path and description.
The caller assigns a file identity by path and supplies its backing contents.
An entry alone supplies no information about aliasing between descriptors. -/
def ofLpsFile (fileId : Nat) : LPS.FdEntry → Option (LPS.Fs.Path × OpenFile)
  | .file path offset => some (path, ⟨fileId, offset.toNat, true, false⟩)
  | .fileW path offset => some (path, ⟨fileId, offset.toNat, false, true⟩)
  | .fileRW path offset => some (path, ⟨fileId, offset.toNat, true, true⟩)
  | _ => none

end Silmaril.Process.AbstractIO
