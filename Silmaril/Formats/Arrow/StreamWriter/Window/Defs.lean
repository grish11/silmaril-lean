module

public import Silmaril.Prelude.Bytes.Defs

@[expose] public section

namespace Silmaril.Formats.Arrow.StreamWriter

/-- A byte tree occurs as an unmodified subtree of another tree. Its position
is the sum of the lengths of the preceding subtrees. -/
inductive Window (part : KBytes) : KBytes → Nat → Prop where
  | self : Window part part 0
  | left {front : KBytes} {offset : Nat} (previous : Window part front offset) (back : KBytes) :
      Window part (front ++ back) offset
  | right (front : KBytes) {back : KBytes} {offset : Nat} (previous : Window part back offset) :
      Window part (front ++ back) (front.len + offset)

end Silmaril.Formats.Arrow.StreamWriter
