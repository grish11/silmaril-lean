module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms

/-! # Contextual binding combinators used by categorical LambdaSSA -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

export Silmaril.Isotope.LetIter.Semantics.Categorical
  (retainLeft_copy copyValue extend_capture extend_capture_assoc
    bind_assoc_capture bind_assoc_reindex bind_case_capture)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
