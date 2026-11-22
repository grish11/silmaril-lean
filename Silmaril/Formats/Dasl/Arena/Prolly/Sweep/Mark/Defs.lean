module

public import Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Arena.Prolly.Sweep

open Silmaril.Semantics.Prolly (Block)

variable {Name Key Payload : Type}

def localId : Handle Name → Option Nat
  | .local index => some index
  | .external _ => none

def localChildren (arena : Indexed Name Key Payload) (index : Nat) : List Nat :=
  match arena.blocks[index]? with
  | some (.branch _ children) => children.filterMap fun child => localId child.2
  | _ => []

def markStep (arena : Indexed Name Key Payload) (index : Nat) (marked : List Nat) : List Nat :=
  if marked.contains index then localChildren arena index ++ marked else marked

/-- Visit each possible index once, descending. A newly discovered child of a
backward edge has yet to be visited. The list represents a set; duplicates from
shared edges need not be removed. No external name is turned into an index. -/
def markBelow (arena : Indexed Name Key Payload) : Nat → List Nat → List Nat
  | 0, marked => marked
  | bound + 1, marked => markBelow arena bound (markStep arena bound marked)

def mark (arena : Indexed Name Key Payload) (roots : List (Handle Name)) : List Nat :=
  markBelow arena arena.blocks.size (roots.filterMap localId)

/-- The existing certificate checker is still the admission boundary. An
unavailable or unchecked closure never returns a partly swept view. -/
def markAndSweep? (arena : Indexed Name Key Payload) (roots : List (Handle Name)) :
    Option (Collected Name Key Payload) := sweep? arena roots (mark arena roots)

/-- Sufficient for the descending marker. Only blocks reachable through local
edges need to exist and have backward local successors. External edges need
neither a local index nor available bytes. -/
def Markable (arena : Indexed Name Key Payload) (roots : List (Handle Name)) : Prop :=
  (∀ index, Reachable arena roots (.local index) → index < arena.blocks.size) ∧
  (∀ index, Reachable arena roots (.local index) → ∀ child ∈ localChildren arena index, child < index)

/-- Enumerate selected outer keys; unmapped keys contribute no root. It covers
the entire directory only when every occupied key is in the enumeration. -/
def directoryRoots {Outer : Type} (directory : Outer → Option (Handle Name)) (keys : List Outer) :
    List (Handle Name) := keys.filterMap directory

def CoversDirectory {Outer : Type} (directory : Outer → Option (Handle Name)) (keys : List Outer) : Prop :=
  ∀ key, (directory key).isSome = true → key ∈ keys

end Silmaril.Formats.Dasl.Arena.Prolly.Sweep
