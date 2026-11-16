module

public import Silmaril.Semantics.StreamBounds.Thms

/-!
# Resource bounds for streaming languages: examples

Concrete item gaps, nesting depths and bound memberships, checked by `decide`. Items are
separated by `0`; brackets are `1` (open) and `2` (close) over `ℕ` tokens.
-/

public section

namespace Silmaril.Streams.Examples

open Silmaril.Streams

/-- Separator `0`. -/
def isZero (a : ℕ) : Bool := a == 0

/-- Token `1` opens, `2` closes, anything else is neutral. -/
def kind12 : ℕ → BracketKind
  | 1 => .opening
  | 2 => .closing
  | _ => .neutral

example : gap isZero [5, 6, 0, 7] = 1 := by decide
example : gap isZero [5, 6, 7] = 3 := by decide
example : gap isZero [5, 6, 0] = 0 := by decide

example : depth kind12 [1, 1, 3, 2] = 1 := by decide
example : depth kind12 [2, 2, 1] = 1 := by decide
example : netDepth kind12 [2, 2, 1] = -1 := by decide

/-- Three items of at most two symbols each. -/
example : [5, 6, 0, 7, 0, 8, 9] ∈ ItemBound isZero 2 := by decide
example : [5, 6, 0, 7, 0, 8, 9] ∉ ItemBound isZero 1 := by decide
example : [5, 6, 0, 7, 0, 8, 9] ∉ RunBound List.length 6 := by decide

example : [1, 1, 2, 1, 2, 2] ∈ DepthBound kind12 2 := by decide
example : [1, 1, 2, 1, 2, 2] ∉ DepthBound kind12 1 := by decide

end Silmaril.Streams.Examples
