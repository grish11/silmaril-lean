module

public import Silmaril.Formats.Dasl.Arena.Prolly.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Arena.Prolly

open Silmaril.Semantics.Prolly (Block)
open Silmaril.Formats.Dasl.Prolly (Fault route)

variable {Name Key Payload Ref Target : Type}

inductive Handle (Name : Type) where
  | local (index : Nat)
  | external (name : Name)
  deriving DecidableEq, Repr

def relabel (map : Ref → Target) : Block Ref Key Payload → Block Target Key Payload
  | .leaf entries => .leaf entries
  | .branch level children => .branch level (children.map fun (key, child) => (key, map child))

def Reader.Refines (source : Reader Ref Key Payload) (map : Ref → Target) (target : Reader Target Key Payload) : Prop :=
  ∀ ⦃ref block⦄, source ref = .ok block → target (map ref) = .ok (relabel map block)

/-- A dense, append-only typed snapshot. Local indices are meaningful only in this
snapshot's append lineage, not globally. External references are a separate lane. -/
structure Indexed (Name Key Payload : Type) where
  blocks : Array (Block (Handle Name) Key Payload)

namespace Indexed

def empty : Indexed Name Key Payload := ⟨#[]⟩

def KnownBefore (bound : Nat) : Handle Name → Prop
  | .local index => index < bound
  | .external _ => True

def admissible (bound : Nat) : Block (Handle Name) Key Payload → Bool
  | .leaf _ => true
  | .branch _ children => children.all fun pair => match pair.2 with
    | .local index => decide (index < bound)
    | .external _ => true

/-- Reject forward local edges. No mechanism clears or overwrites an index. -/
def append? (arena : Indexed Name Key Payload) (block : Block (Handle Name) Key Payload) :
    Option (Indexed Name Key Payload × Nat) :=
  if admissible arena.blocks.size block then some (⟨arena.blocks.push block⟩, arena.blocks.size) else none

/-- Caller-supplied localization. An unselected name stays external. -/
def localize (locate : Name → Option Nat) (block : Block Name Key Payload) : Block (Handle Name) Key Payload :=
  relabel (fun name => (locate name).elim (.external name) .local) block

/-- Read faults pass through unchanged. `ok none` means the proposed localization
would introduce a forward local edge, not that the requested data was absent. -/
def acquire (arena : Indexed Name Key Payload) (source : Reader Name Key Payload) (locate : Name → Option Nat)
    (name : Name) : Except (Fault Name) (Option (Indexed Name Key Payload × Nat)) :=
  (source name).map fun block => arena.append? (localize locate block)

def read (arena : Indexed Name Key Payload) (external : Reader Name Key Payload) : Reader (Handle Name) Key Payload
  | .local index => match arena.blocks[index]? with
    | none => .error (.missing (.local index))
    | some block => .ok block
  | .external name => match external name with
    | .ok block => .ok (relabel Handle.external block)
    | .error (.missing ref) => .error (.missing (.external ref))
    | .error (.fuel ref) => .error (.fuel (.external ref))
    | .error (.invalidWire ref) => .error (.invalidWire (.external ref))
    | .error (.invalidNode ref) => .error (.invalidNode (.external ref))

def lookup [LinearOrder Key] (arena : Indexed Name Key Payload) (external : Reader Name Key Payload)
    (width fuel root : Nat) (key : Key) : Except (Fault (Handle Name)) (Option Payload) :=
  route (arena.read external) width key fuel none (.local root)

/-- Naming is separate from reading or allocating. Preserve external names; only
reconstruct local blocks. A failed name choice or inadequate fuel gives `none`. -/
def name? (arena : Indexed Name Key Payload) (choose : Block Name Key Payload → Option Name) :
    Nat → Handle Name → Option Name
  | _, .external name => some name
  | 0, .local _ => none
  | fuel + 1, .local index => do
    match ← arena.blocks[index]? with
    | .leaf entries => choose (.leaf entries)
    | .branch level children =>
      let named ← children.mapM fun (key, child) => (arena.name? choose fuel child).map (key, ·)
      choose (.branch level named)

/-- Eager reference implementation: evaluate the same choice at every index
up front. This shares cached results with readers, not work between roots. -/
def eagerNames (arena : Indexed Name Key Payload) (choose : Block Name Key Payload → Option Name) (fuel : Nat) :
    Array (Option Name) :=
  Array.ofFn fun index : Fin arena.blocks.size => arena.name? choose fuel (.local index)

end Indexed
end Silmaril.Formats.Dasl.Arena.Prolly
