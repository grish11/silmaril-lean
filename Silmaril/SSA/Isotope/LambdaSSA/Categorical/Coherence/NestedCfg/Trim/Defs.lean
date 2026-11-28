module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Defs

/-! # Retain selected CFG labels, then append the unchanged exits -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

/-- Embed the retained local indices and shift the entire outward suffix to
start after the original local family. Nested CFGs lift this map past their
own local labels. -/
def retainLabelIndex {m n : Nat} (keep : Fin m ↪ Fin n) (i : Nat) : Nat :=
  if h : i < m then (keep ⟨i, h⟩).val else n + (i - m)

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
