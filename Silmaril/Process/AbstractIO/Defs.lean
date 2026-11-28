module

public import Silmaril.Process.ITreeTrace.Defs
public import Silmaril.Process.Syscall
public import Silmaril.Semantics.ITreeInterpret.Defs

/-! Byte-valued operations on preinstalled regular files and connected streams. -/

@[expose] public section

namespace Silmaril.Process.AbstractIO

open TypedSyscall (Signature Kernel)
open ITreeTrace (Event Exchange Program)
open Silmaril.Elgot.ITree (trigger)

abbrev Bytes := List Byte

inductive Request where
  | read (fd count : Nat)
  | write (fd : Nat) (bytes : Bytes)
  | pread (fd offset count : Nat)
  | pwrite (fd offset : Nat) (bytes : Bytes)
  | recv (fd count : Nat)
  | send (fd : Nat) (bytes : Bytes)
  deriving DecidableEq, Repr

inductive Received where
  | data (bytes : Bytes)
  | zeroRequest
  | eof
  | wouldBlock
  deriving DecidableEq, Repr

inductive Sent where
  | count (accepted : Nat)
  | wouldBlock
  deriving DecidableEq, Repr

abbrev IOResult := Except Syscall.Errno

def Response : Request → Type
  | .read .. | .pread .. => IOResult Bytes
  | .write .. | .pwrite .. => IOResult Nat
  | .recv .. => IOResult Received
  | .send .. => IOResult Sent

def signature : Signature := ⟨Request, Response⟩

abbrev Prog := Program signature
abbrev Observation := Exchange signature

def call (req : Request) : Prog (Response req) :=
  trigger (Event.call (sig := signature) req)

/-- Multiple descriptors may name the same open file description. Independent
opens of the same file use separate descriptions, with separate offsets. -/
inductive Descriptor where
  | file (description : Nat)
  | stream (socket : Nat)
  deriving DecidableEq, Repr

structure OpenFile where
  file : Nat
  offset : Nat
  readable : Bool
  writable : Bool
  deriving DecidableEq, Repr

/-- The receive queue and peer FIN are supplied initially. `sendRoom` counts
bytes that may still be queued locally, and `tx` records accepted bytes. -/
structure Stream where
  rx : Bytes := []
  peerFinished : Bool := false
  tx : Bytes := []
  sendRoom : Nat := 0
  deriving DecidableEq, Repr

structure Store where
  fds : Nat → Option Descriptor := fun _ => none
  descriptions : Nat → Option OpenFile := fun _ => none
  files : Nat → Option Bytes := fun _ => none
  streams : Nat → Option Stream := fun _ => none

def eAgain : Syscall.Errno := ⟨11, by decide, by decide⟩
def eNotSocket : Syscall.Errno := ⟨88, by decide, by decide⟩
def eIllegalSeek : Syscall.Errno := ⟨29, by decide, by decide⟩

/-- Select a positive per-call cap, bounded by the existing Linux transfer cap. -/
def transferCap (choice : Nat) : Nat := min (choice + 1) Syscall.maxTransfer

/-- Overwrite the selected interval, preserving the suffix and filling a hole
with zero bytes. An empty write leaves the file untouched. -/
def overwrite (data : Bytes) (offset : Nat) (bytes : Bytes) : Bytes :=
  if bytes.isEmpty then data
  else data.take offset ++ List.replicate (offset - data.length) 0 ++ bytes ++
    data.drop (offset + bytes.length)

def fileEntry (s : Store) (fd : Nat) (position : Option Nat) (writing : Bool) :
    IOResult (Nat × OpenFile × Bytes) := do
  match s.fds fd with
  | some (.file id) =>
    let some desc := s.descriptions id | throw Syscall.Errno.badDescriptor
    if !(if writing then desc.writable else desc.readable) then
      throw Syscall.Errno.badDescriptor
    let some data := s.files desc.file | throw Syscall.Errno.badDescriptor
    pure (id, desc, data)
  | some (.stream _) => throw (if position.isSome then eIllegalSeek else Syscall.Errno.badDescriptor)
  | none => throw Syscall.Errno.badDescriptor

def streamEntry (s : Store) (fd : Nat) : IOResult (Nat × Stream) :=
  match s.fds fd with
  | some (.stream id) =>
    match s.streams id with
    | some stream => .ok (id, stream)
    | none => .error Syscall.Errno.badDescriptor
  | some (.file _) => .error eNotSocket
  | none => .error Syscall.Errno.badDescriptor

def advance (s : Store) (id : Nat) (desc : OpenFile) (position : Option Nat)
    (count : Nat) : Store :=
  if position.isSome then s
  else
    let desc := { desc with offset := desc.offset + count }
    { s with descriptions := Function.update s.descriptions id (some desc) }

def readFile (choice : Nat) (s : Store) (fd count : Nat) (position : Option Nat) :
    IOResult Bytes × Store :=
  match fileEntry s fd position false with
  | .error error => (.error error, s)
  | .ok (id, desc, data) =>
    let delivered := (data.drop (position.getD desc.offset)).take (min count (transferCap choice))
    (.ok delivered, advance s id desc position delivered.length)

def writeFile (choice : Nat) (s : Store) (fd : Nat) (bytes : Bytes)
    (position : Option Nat) : IOResult Nat × Store :=
  match fileEntry s fd position true with
  | .error error => (.error error, s)
  | .ok (id, desc, data) =>
    let accepted := bytes.take (transferCap choice)
    let after := advance s id desc position accepted.length
    let contents := overwrite data (position.getD desc.offset) accepted
    (.ok accepted.length, { after with files := Function.update after.files desc.file (some contents) })

def receive (choice : Nat) (s : Store) (fd count : Nat) : IOResult Received × Store :=
  match streamEntry s fd with
  | .error error => (.error error, s)
  | .ok (id, stream) =>
    if count = 0 then (.ok .zeroRequest, s)
    else if stream.rx.isEmpty then
      (.ok (if stream.peerFinished then .eof else .wouldBlock), s)
    else
      let limit := min count (transferCap choice)
      let next := { stream with rx := stream.rx.drop limit }
      (.ok (.data (stream.rx.take limit)), { s with streams := Function.update s.streams id (some next) })

def send (choice : Nat) (s : Store) (fd : Nat) (bytes : Bytes) : IOResult Sent × Store :=
  match streamEntry s fd with
  | .error error => (.error error, s)
  | .ok (id, stream) =>
    if bytes.isEmpty then (.ok (.count 0), s)
    else if stream.sendRoom = 0 then (.ok .wouldBlock, s)
    else
      let accepted := bytes.take (min stream.sendRoom (transferCap choice))
      let next := { stream with tx := stream.tx ++ accepted, sendRoom := stream.sendRoom - accepted.length }
      (.ok (.count accepted.length), { s with streams := Function.update s.streams id (some next) })

/-- One atomic call at an explicit transfer choice. Calls always return in
this nonblocking profile. Would-block is a reply with an unchanged store. -/
def step (choice : Nat) (s : Store) : (req : Request) → Response req × Store
  | .read fd count =>
    match s.fds fd with
    | some (.stream _) =>
      let (reply, after) := receive choice s fd count
      (reply >>= fun
        | .data bytes => .ok bytes
        | .zeroRequest | .eof => .ok []
        | .wouldBlock => .error eAgain, after)
    | _ => readFile choice s fd count none
  | .write fd bytes =>
    match s.fds fd with
    | some (.stream _) =>
      let (reply, after) := send choice s fd bytes
      (reply >>= fun
        | .count n => .ok n
        | .wouldBlock => .error eAgain, after)
    | _ => writeFile choice s fd bytes none
  | .pread fd offset count => readFile choice s fd count (some offset)
  | .pwrite fd offset bytes => writeFile choice s fd bytes (some offset)
  | .recv fd count => receive choice s fd count
  | .send fd bytes => send choice s fd bytes

/-- The same kernel drives sequential and interleaved threads. Each completion
logs its typed request and reply, including modeled errors and would-block. -/
def kernel : Kernel signature Store Observation := fun req before label completion =>
  ∃ choice, label = ⟨req, (step choice before req).1⟩ ∧
    completion = .returned (step choice before req).1 (step choice before req).2

/-- Syntactic policy for code that only reads at explicit file positions. -/
def PositionedReads : Request → Prop
  | .pread .. => True
  | _ => False

end Silmaril.Process.AbstractIO
