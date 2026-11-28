module

public import Silmaril.Logic.Temporal.TLA.ProofFrontEnd.Defs

namespace Silmaril.Proofs.Logic.Temporal.TLA.ProofFrontEnd

open Silmaril.Logic.Temporal.TLA.ProofFrontEnd
open Silmaril.Logic.Temporal.TLA.DataElab

universe u

public theorem exact_sound {V : Type u} {obligation : Obligation}
    (certificate : ExactCertificate obligation) (model : Interpretation V) :
    obligation.Valid model := by
  intro valuation assumptions _
  have premise := assumptions certificate.premise certificate.inScope
  unfold Proposition.holds CheckedExpr.eval at premise ⊢
  rw [← certificate.termEq]
  exact premise

end Silmaril.Proofs.Logic.Temporal.TLA.ProofFrontEnd
