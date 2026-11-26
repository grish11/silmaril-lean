module

public import Silmaril.Process.AbstractIO.Defs
public import Silmaril.Process.ITreeTrace.Thms
public import Silmaril.Semantics.ITreeInterpret.Thms

/-! File and byte-stream APIs interpreted into the abstract syscall tree. -/

@[expose] public section

namespace Silmaril.Process.AbstractIO

open TypedSyscall (Signature)
open ITreeTrace (Event Program)
open Silmaril.Elgot.ITree

structure FilePosition where
  fd : Nat
  offset : Nat

inductive FileRequest where
  | copyChunk (source destination : FilePosition) (count : Nat)

def fileSignature : Signature := ⟨FileRequest, fun _ => IOResult Nat⟩

/-- At most one positioned read and one positioned write. Return the actual
written count. An empty read skips the write. Any error ends the operation. -/
def copyChunk (source destination : FilePosition) (count : Nat) : Prog (IOResult Nat) := do
  match ← call (.pread source.fd source.offset count) with
  | .error errno => pure (.error errno)
  | .ok [] => pure (.ok 0)
  | .ok bytes => call (.pwrite destination.fd destination.offset bytes)

def fileHandler : Handler (Event fileSignature) Prog := fun {_} event =>
  match event with
  | .call (FileRequest.copyChunk source destination count) => copyChunk source destination count

noncomputable def fileAPI : Interpret.Hom (E := Event fileSignature) (m := Prog) fileHandler :=
  Interpret.foldHom (E := Event fileSignature) (m := Prog) fileHandler

inductive NetworkRequest where
  | sendChunk (fd : Nat) (bytes : Bytes)
  | receiveChunk (fd count : Nat)

inductive SendProgress where
  | remainder (unsent : Bytes)
  | wouldBlock
  deriving DecidableEq, Repr

def NetworkResponse : NetworkRequest → Type
  | .sendChunk .. => IOResult SendProgress
  | .receiveChunk .. => IOResult Received

def networkSignature : Signature := ⟨NetworkRequest, NetworkResponse⟩

/-- Make a single send attempt. An accepted prefix leaves the unsent suffix
with the caller. Would-block leaves the entire original chunk with the caller. -/
def sendChunk (fd : Nat) (bytes : Bytes) : Prog (IOResult SendProgress) := do
  match ← call (.send fd bytes) with
  | .error errno => pure (.error errno)
  | .ok .wouldBlock => pure (.ok .wouldBlock)
  | .ok (.count n) => pure (.ok (.remainder (bytes.drop n)))

def networkHandler : Handler (Event networkSignature) Prog := fun {_} event =>
  match event with
  | .call (NetworkRequest.sendChunk fd bytes) => sendChunk fd bytes
  | .call (NetworkRequest.receiveChunk fd count) => call (.recv fd count)

noncomputable def networkAPI : Interpret.Hom (E := Event networkSignature) (m := Prog) networkHandler :=
  Interpret.foldHom (E := Event networkSignature) (m := Prog) networkHandler

end Silmaril.Process.AbstractIO
