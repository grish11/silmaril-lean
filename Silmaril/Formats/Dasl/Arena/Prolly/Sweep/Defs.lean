module

public import Silmaril.Formats.Dasl.Arena.Prolly.Index.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Arena.Prolly.Sweep

open Silmaril.Semantics.Prolly (Block)

variable {Name Key Payload : Type}

def kept (indices : List Nat) : Handle Name → Bool
  | .local index => indices.contains index
  | .external _ => true

def closed (indices : List Nat) : Block (Handle Name) Key Payload → Bool
  | .leaf _ => true
  | .branch _ children => children.all fun child => kept indices child.2

def check (arena : Indexed Name Key Payload) (roots : List (Handle Name)) (indices : List Nat) : Bool :=
  roots.all (kept indices) && indices.all fun index =>
    (arena.blocks[index]?).any (closed indices)

inductive Reachable (arena : Indexed Name Key Payload) (roots : List (Handle Name)) : Handle Name → Prop where
  | root {ref : Handle Name} : ref ∈ roots → Reachable arena roots ref
  | child {index level : Nat} {children : List (Key × Handle Name)} {edge : Key × Handle Name} :
    Reachable arena roots (.local index) → arena.blocks[index]? = some (.branch level children) → edge ∈ children →
    Reachable arena roots edge.2

/-- Sweeping preserves the index address space. Outer `none` from array lookup
means out of bounds; `some none` is a reclaimed slot. No API reuses a hole. -/
structure Collected (Name Key Payload : Type) where
  slots : Array (Option (Block (Handle Name) Key Payload))

namespace Collected

def read (view : Collected Name Key Payload) (external : Reader Name Key Payload) : Reader (Handle Name) Key Payload
  | .local index => match view.slots[index]?.join with
    | none => .error (.missing (.local index))
    | some block => .ok block
  | .external name => Indexed.empty.read external (.external name)

end Collected

/-- Check a conservative finite mark certificate; the set may retain more
than the least reachable subset. The outer CAS is neither read nor swept. -/
def sweep? (arena : Indexed Name Key Payload) (roots : List (Handle Name)) (indices : List Nat) :
    Option (Collected Name Key Payload) :=
  if check arena roots indices then
    some ⟨Array.ofFn fun index : Fin arena.blocks.size =>
      if indices.contains index.val then some arena.blocks[index] else none⟩
  else none

end Silmaril.Formats.Dasl.Arena.Prolly.Sweep
