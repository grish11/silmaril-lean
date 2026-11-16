module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Computation.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.DependentTelescope
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WHypotheticalComputation

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.HypotheticalExamples

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- The result carrier depends on the first source argument; its Unit instantiation is an actual hypothesis leaf. -/
theorem dependent_identity_beta : Ctx.nil.JEqB 2 (ContextClosure basis) .unit
    (.app (.app (.abs (.univ 0) (.abs (.bv 0) (.bv 0))) .unit) .star) .star :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WHypotheticalComputation.dependent_identity_beta

/-- The original root computes on an actual W leaf formed from the hypothesis-bearing descriptor. -/
theorem nullary_root_beta : Ctx.nil.JEqB 2 (ContextClosure basis) .unit
    (nullaryDescription.root nullaryRawLeaf) .star :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WHypotheticalComputation.nullary_root_beta

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.HypotheticalExamples
