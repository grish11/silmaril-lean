module

public import Silmaril.Process.AbstractIO.API.Defs
public import Silmaril.Process.ITreeTrace.Exact.Defs

/-! Exact single-exchange lowering and observation of the abstract Linux I/O model. -/

@[expose] public section

namespace Silmaril.Process.AbstractIO.Exact

open Silmaril.Elgot.ITree (Tree ret vis)
open Silmaril.Elgot.ITree.Exact (Kernel Sentence)
open ITreeTrace (Event)

abbrev profile := ITreeTrace.Exact.profile Store Observation
abbrev target := ITreeTrace.Exact.eventSignature signature

/-- Preserve every transfer choice and the label carrying the concrete request and typed reply.
Descriptor errors and would-block are replies in this model. -/
abbrev linuxKernel : Kernel profile target := ITreeTrace.Exact.kernel AbstractIO.kernel

inductive PositionedRequest where
  | read (atFile : FilePosition) (count : Nat)
  | write (atFile : FilePosition) (bytes : Bytes)

def PositionedResponse : PositionedRequest → Type
  | .read .. => IOResult Bytes
  | .write .. => IOResult Nat

abbrev positionedSignature : TypedSyscall.Signature := ⟨PositionedRequest, PositionedResponse⟩

def positionedCalls : positionedSignature.Hom signature where
  request
    | .read p count => .pread p.fd p.offset count
    | .write p bytes => .pwrite p.fd p.offset bytes
  response
    | .read .. | .write .. => id

abbrev positioned := ITreeTrace.Exact.eventSignature positionedSignature

/-- An explicit program of positioned operations. Every event has one target exchange. -/
def positionedCopy (src dst : FilePosition) (count : Nat) :
    Tree positioned.Event (IOResult Nat) :=
  vis (Event.call (sig := positionedSignature) (.read src count)) fun
    | .error errno => ret (.error errno)
    | .ok [] => ret (.ok 0)
    | .ok bytes => vis (Event.call (sig := positionedSignature) (.write dst bytes)) ret

/-- Each nonblocking network API event uses a single exchange.
Send reports the unsent suffix, while receive keeps the full typed reply. -/
def networkCalls : networkSignature.Hom signature where
  request
    | .sendChunk fd bytes => .send fd bytes
    | .receiveChunk fd count => .recv fd count
  response
    | .sendChunk _ bytes => fun
      | .error errno => .error errno
      | .ok .wouldBlock => .ok .wouldBlock
      | .ok (.count n) => .ok (.remainder (bytes.drop n))
    | .receiveChunk .. => id

/-- Test the positioned copy under an explicit initial-store assumption. -/
def copySentence (src dst : FilePosition) (count : Nat) (pre : Store → Prop)
    (post : Store → Silmaril.Elgot.ITree.Exact.Observation profile (IOResult Nat) → Prop) :
    Sentence profile positioned where
  Return := IOResult Nat
  test := positionedCopy src dst count
  pre _ := pre
  post _ := post

end Silmaril.Process.AbstractIO.Exact
