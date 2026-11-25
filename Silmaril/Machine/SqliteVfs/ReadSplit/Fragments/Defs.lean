module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.ReadSplit.Fragments

/-- Serial calls on a nonempty list of fragments report their actual trace,
the returned handler state, and a merged reply when all buffers are available. -/
structure FragmentOutcome (State : Type) where
  reply : Option ReadReply
  file : State
  trace : Trace

/-- The count and rest arguments represent a nonempty sequence. All requests
are issued in order, including a zero count or calls after an error. A reply
without a buffer makes the aggregate absent. The typed trace keeps it. -/
def readFragments {State : Type} (step : Handler State) (handle : Handle)
    (state : State) (offset count : Nat) (rest : List Nat) : FragmentOutcome State :=
  let request := Request.read handle offset count
  let (reply, after) := step state request
  match rest with
  | [] => ⟨combine (.ok []) reply, after, [⟨request, reply⟩]⟩
  | next :: rest =>
    let later := readFragments step handle after (offset + count) next rest
    ⟨later.reply.bind (combine reply), later.file, ⟨request, reply⟩ :: later.trace⟩

/-- The file offsets of the requested fragments are their preceding
cumulative sizes, measured from the initial offset. -/
def fragmentRequests (handle : Handle) (offset : Nat) : List Nat → List Request
  | [] => []
  | count :: rest => .read handle offset count :: fragmentRequests handle (offset + count) rest

end Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
