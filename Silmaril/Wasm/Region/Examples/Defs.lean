module

public import Silmaril.Wasm.Region.ByteMap.Thms
public import Silmaril.Wasm.Region.Operational.Thms

@[expose] public section
namespace Silmaril.Wasm.Region.Examples

/-- Encoded function body: one i32 local group, two nops, return, end.
Body offsets include all three locals bytes and exclude the code size prefix. -/
def repeated : ByteMap.Input :=
  ⟨7, [1, 1, 0x7F, 1, 1, 0x0F, 0x0B], 3, [(1, .num (.int .i32))],
    [.nop, .nop, .return_]⟩

def rootRow (index start stop : Nat) (h : start ≤ stop) : ByteMapEntry :=
  ⟨⟨7, [], index⟩, ⟨start, stop, h⟩⟩

def repeatedRows : List ByteMapEntry :=
  [rootRow 0 3 4 (by decide), rootRow 1 4 5 (by decide), rootRow 2 5 6 (by decide)]

/-- A structured block occupies its entire encoded span, including `end`.
Its inner nop needs a future nested-map producer; it is not another root row. -/
def structured : ByteMap.Input :=
  ⟨7, [0, 2, 0x40, 1, 0x0B, 0x0F, 0x0B], 1, [], [.block .empty [.nop], .return_]⟩

def structuredRows : List ByteMapEntry :=
  [rootRow 0 1 5 (by decide), rootRow 1 5 6 (by decide)]

end Silmaril.Wasm.Region.Examples
