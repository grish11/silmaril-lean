module

public import Silmaril.Wasm.Region.ByteMap.Nested.Thms

/-! # Deterministic nested body-byte fixtures

Offsets include the locals vector and exclude delimiter instructions. These
small source bodies are fixtures, not measured module-corpus coverage.
-/

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.Nested.Examples
open Silmaril.Machine.Region (Range)

def r (start stop : Nat) : Range := ⟨start, max start stop, Nat.le_max_left _ _⟩

def nested : Input :=
  ⟨7, [0, 0x02, 0x40, 0x03, 0x40, 0x01, 0x0B, 0x0B, 0x0B], 1, [],
    [.block .empty [.loop .empty [.nop]]]⟩

def outer : Frame := ⟨0, 0, r 1 8, 0, ⟨[0x40], [0x03, 0x40, 0x01, 0x0B], none⟩⟩
def inner : Frame := ⟨0, 0, r 3 7, 0, ⟨[0x40], [0x01], none⟩⟩

def nestedTable : List Candidate :=
  [⟨⟨⟨7, [], 0⟩, r 1 8⟩, []⟩,
   ⟨⟨⟨7, [(0, 0)], 0⟩, r 3 7⟩, [outer]⟩,
   ⟨⟨⟨7, [(0, 0), (0, 0)], 0⟩, r 5 6⟩, [outer, inner]⟩]

def conditional : Input :=
  ⟨8, [0, 0x04, 0x40, 0x01, 0x05, 0x01, 0x0B, 0x0B], 1, [],
    [.if_ .empty [.nop] [.nop]]⟩

def arm (which : Nat) : Frame := ⟨0, 0, r 1 7, which, ⟨[0x40], [0x01], some [0x01]⟩⟩
def conditionalTable : List Candidate :=
  [⟨⟨⟨8, [], 0⟩, r 1 7⟩, []⟩,
   ⟨⟨⟨8, [(0, 0)], 0⟩, r 3 4⟩, [arm 0]⟩,
   ⟨⟨⟨8, [(0, 1)], 0⟩, r 5 6⟩, [arm 1]⟩]

def handler : Input :=
  ⟨9, [0, 0x1F, 0x40, 0, 0x01, 0x0B, 0x0B], 1, [], [.tryTable .empty [] [.nop]]⟩

def handlerFrame : Frame := ⟨0, 0, r 1 6, 0, ⟨[0x40, 0], [0x01], none⟩⟩
def handlerTable : List Candidate :=
  [⟨⟨⟨9, [], 0⟩, r 1 6⟩, []⟩, ⟨⟨⟨9, [(0, 0)], 0⟩, r 4 5⟩, [handlerFrame]⟩]

/-- The block opener is instruction 1 but segment 0; CFG paths use the latter. -/
def prefixed : Input :=
  ⟨10, [0, 0x01, 0x02, 0x40, 0x01, 0x0B, 0x0B], 1, [], [.nop, .block .empty [.nop]]⟩

def prefixedFrame : Frame := ⟨0, 1, r 2 6, 0, ⟨[0x40], [0x01], none⟩⟩
def prefixedTable : List Candidate :=
  [⟨⟨⟨10, [], 0⟩, r 1 2⟩, []⟩, ⟨⟨⟨10, [], 1⟩, r 2 6⟩, []⟩,
   ⟨⟨⟨10, [(0, 0)], 0⟩, r 4 5⟩, [prefixedFrame]⟩]

def noElse : Input :=
  ⟨11, [0, 0x04, 0x40, 0x01, 0x0B, 0x0B], 1, [], [.if_ .empty [.nop] []]⟩

def noElseFrame : Frame := ⟨0, 0, r 1 5, 0, ⟨[0x40], [0x01], none⟩⟩

end Silmaril.Wasm.Region.ByteMap.Nested.Examples
