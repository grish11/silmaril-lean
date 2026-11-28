module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.SourceSemantics.Thms

/-! # The elaborated graph at a literal count of blocks

The elaborated lowering of a φ graph has as many blocks as the φ graph,
as the length of a list. The fragment of flat graphs with a checked
table is stated for a count of the form `size + 1`. `recount` is the same
flat graph at an equal count.
-/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceReadback

open LambdaSSA (FiniteCFG)

universe v

variable {Φ : Type v} {a b exits n : Nat}

/-- The same flat graph at an equal count of blocks. -/
def recount (count : a = b) (g : FiniteCFG Φ a exits n) : FiniteCFG Φ b exits n :=
  count ▸ g

end Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceReadback
