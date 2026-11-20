module

public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Stream.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Waitable.Defs
public import Silmaril.Wasm.Component.Reference.WIT.Interp.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Async

open Silmaril.Wasm.Component Silmaril.Wasm.Component.AsyncRef Silmaril.Wasm.Component.ABI
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

abbrev Element := Option (WIT.ClosedType RtId)

/-- A typed endpoint identifies an object in the component arena, not a recyclable guest
handle slot. The running component store determines its liveness and ownership. -/
structure Endpoint (kind : EndKind) (element : Element) where
  id : EndId

def endpointEnv (base : WIT.Env Empty RtId) : WIT.Env Empty RtId :=
  base.withEndpoints (Endpoint .readableFuture) (Endpoint .readableStream)

variable {E : CoreEngine} {World : Type}

/-- Resolve a guest table slot at the reference machine's dynamic type boundary.
This identifies an end without copying or transferring it. -/
def Endpoint.inspect (kind : EndKind) (element : Element) (inst : InstId) (slot : Nat) :
    P E World (Endpoint kind element) := do
  let (endpoint, _) ← Builtins.expectEnd kind element (← handlesGet inst slot)
  return ⟨endpoint⟩

inductive Channel where
  | stream
  | future
  deriving DecidableEq, Repr

inductive Side where
  | read
  | write
  deriving DecidableEq, Repr

def Channel.endKind : Channel → Side → EndKind
  | .stream, .read => .readableStream
  | .stream, .write => .writableStream
  | .future, .read => .readableFuture
  | .future, .write => .writableFuture

/-- Calls of the async Component Model built-ins. Slots and pointers are ABI operands;
the WIT values are `Endpoint`s. Future copying has length one, never a stream length. -/
inductive Call (E : CoreEngine) where
  | create (channel : Channel) (element : Element)
  | streamCopy (side : Side) (element : Element) (opts : CanonOpts E) (slot ptr length : Nat)
  | futureCopy (side : Side) (element : Element) (opts : CanonOpts E) (slot ptr : Nat)
  | cancel (channel : Channel) (side : Side) (element : Element) (async_ : Bool) (slot : Nat)
  | close (channel : Channel) (side : Side) (element : Element) (slot : Nat)
  | createSet
  | join (slot setSlot : Nat)
  | poll (mem : E.MemAddr) (setSlot ptr : Nat)
  | wait (mem : E.MemAddr) (setSlot ptr : Nat)
  | closeSet (setSlot : Nat)

/-- Use the actual reference built-ins for copies, readiness, cancellation and drop. This
retains their effects and traps, including earlier operations in the same execution. -/
def Call.program (limits : Component.Limits) (quirks : Quirks) : Call E → P E World (List FlatValue)
  | .create channel element => Builtins.newBuiltin limits (channel.endKind .read) element
  | .streamCopy side element opts slot ptr length =>
    Builtins.copyBuiltin limits quirks (Channel.stream.endKind side) element opts slot ptr length
  | .futureCopy side element opts slot ptr =>
    Builtins.copyBuiltin limits quirks (Channel.future.endKind side) element opts slot ptr 1
  | .cancel channel side element async_ slot =>
    Builtins.cancelCopy limits (channel.endKind side) element async_ slot
  | .close channel side element slot => Builtins.dropEnd limits (channel.endKind side) element slot
  | .createSet => Builtins.waitableSetNew limits
  | .join slot setSlot => Builtins.waitableJoin limits slot setSlot
  | .poll mem setSlot ptr => Builtins.waitableSetPoll limits mem setSlot ptr
  | .wait mem setSlot ptr => Builtins.waitableSetWait limits mem setSlot ptr
  | .closeSet setSlot => Builtins.waitableSetDrop limits setSlot

/-- Extend an existing synchronous API without translating any of its operations. -/
abbrev ExtendedCall (E : CoreEngine) (Base : Type) := Base ⊕ Call E

def program {Base : Type} (base : Base → P E World (List FlatValue)) (limits : Component.Limits)
    (quirks : Quirks) : ExtendedCall E Base → P E World (List FlatValue)
  | .inl ordinary => base ordinary
  | .inr asyncCall => asyncCall.program limits quirks

def runCalls {Base : Type} (base : Base → P E World (List FlatValue)) (limits : Component.Limits)
    (quirks : Quirks) (calls : List (ExtendedCall E Base)) : P E World (List (List FlatValue)) :=
  Prog.mapM (program base limits quirks) calls

end Silmaril.Wasm.Game.HandleAccept.Wit.Async
